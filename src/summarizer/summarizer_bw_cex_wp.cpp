/*******************************************************************\

Module: Slicing-based WP Counterexample-based Backward Analysis

Author: Madhukar Kumar, Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_dependency_graph.h"

#include "summarizer_bw_cex_wp.h"

/*******************************************************************\

Function: summarizer_bw_cex_wpt::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_wpt::summarize
(
 const function_namet &entry_function)
{
  // no dependencies to begin with
  find_symbols_sett dependency_set;

  status() << "\nSummarizing function " << entry_function << eom;
  compute_summary_rec(entry_function,dependency_set,-1,
		      summaryt::entry_call_site);
}

/*******************************************************************\

Function: summarizer_bw_cex_wpt::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_wpt::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis (WP)..." << eom;
  error_assertion = _error_assertion;
  /*
  std::cout << "error assertion: "
	    << from_expr(ssa_db.get(entry_function).ns, "", error_assertion)
	    << "\n";
  */
  summarize(entry_function);
}


/*******************************************************************\

Function: summarizer_bw_cex_wpt::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

find_symbols_sett summarizer_bw_cex_wpt::inline_summaries
(
 const function_namet &function_name,
 const find_symbols_sett &dependency_set,
 int counter,
 exprt &error_summary)
{
  exprt::operandst slice;

  local_SSAt &SSA = ssa_db.get(function_name);
  //solver << SSA.get_enabling_exprs();
  
  exprt::operandst loophead_selects;
  get_loophead_selects(SSA,ssa_unwinder.get(function_name),*solver.solver,loophead_selects);
  exprt c = conjunction(loophead_selects);

  //std::cout << "Solver <-- " << function_name << ": (conjunction of loophead_selects):"
  //	    << "\t original info ~ " << from_expr(ssa_db.get(function_name).ns, "", c) << "\n";

  slice.push_back(c);
  ssa_inliner.rename(c, counter);

#if 0
  std::cout << "Solver <-- " << function_name << ": (conjunction of loophead_selects):"
  	    << "\t  renamed info ~ " << from_expr(ssa_db.get(function_name).ns, "", c) << "\n";
#endif

  solver << c;

  ssa_dependency_grapht &ssa_depgraph = ssa_db.get_depgraph(function_name);
  
  struct worknodet{
    int node_index;
    find_symbols_sett dependency_set;
  };
  
  worknodet start_node;
  start_node.node_index = 0;
  start_node.dependency_set = dependency_set;

  typedef std::list<worknodet> worklistt;
  worklistt worklist, work_waitlist;
  std::vector<int> covered_nodes;
  
  worklist.push_back(start_node);
  
  while(!worklist.empty()){
    
    /*
    std::cout << "worklist: ";
    for(worklistt::const_iterator w_it=worklist.begin();
	w_it != worklist.end(); w_it++){
      std::cout << w_it->node_index << " ";
    }
    std::cout << "\n";
    
    std::cout << "\t waitlist: ";
    for(worklistt::const_iterator w_it=work_waitlist.begin();
	w_it != work_waitlist.end(); w_it++){
      std::cout << w_it->node_index << " ";
    }
    std::cout << "\n";
    */

    worknodet &worknode = worklist.front();
    
    //std::cout << "working node: " << function_name << ": " << worknode.node_index << "\n";
    /////////////////////////////////////////////////////////////////////////////////////
    //std::cout << "\t size of dependency set: " << worknode.dependency_set.size() << "\n";
    /*
    std::cout << "\t dependency set: ";
    for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	d_it != worknode.dependency_set.end(); d_it++){
      std::cout << *d_it;
    }
    std::cout << "\n\n\n";
    */
    /////////////////////////////////////////////////////////////////////////////////////


    // return if the top most node is reached
    if(worknode.node_index == ssa_depgraph.top_node_index)
    {
      find_symbols_sett vars = worknode.dependency_set;
      vars.insert(dependency_set.begin(), dependency_set.end());
      error_summary = simplify_summary(SSA.ns, conjunction(slice), vars);
      return worknode.dependency_set;
    }
    
    // modify worknode_dependency_set if the node is an assertion
    if(ssa_depgraph.depnodes_map[worknode.node_index].is_assertion == true){

      //std::cout << "\t\t an assertion node\n";
      for(find_symbols_sett::const_iterator d_it = ssa_depgraph.depnodes_map[worknode.node_index].used_symbols.begin();
	  d_it != ssa_depgraph.depnodes_map[worknode.node_index].used_symbols.end(); d_it++){
	worknode.dependency_set.insert(*d_it);
      }

      /////////////////////////////////////////////////////////////////////////////////////
      /*
      std::cout << "\t size of dependency set: " << worknode.dependency_set.size() << "\n";

      std::cout << "\t dependency set: ";
      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	  d_it != worknode.dependency_set.end(); d_it++){
	std::cout << *d_it;
      }
      std::cout << "\n";
      */
      /////////////////////////////////////////////////////////////////////////////////////

      

    }

    // if this is a function call
    if(ssa_depgraph.depnodes_map[worknode.node_index].is_function_call == true){
      //std::cout << "fcall: working node: " << function_name << ": " << worknode.node_index << "\n";
      irep_idt fname = 
	to_symbol_expr((to_function_application_expr(ssa_depgraph.depnodes_map[worknode.node_index].node_info)).function()).get_identifier();
     
      find_symbols_sett renamed_dependencies;

      /////////////////////////////////////////////////////////////////////////////////////
      /*
      std::cout << "\t size of dependency set: " << worknode.dependency_set.size() << "\n";

      std::cout << "\t dependency set: ";
      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	  d_it != worknode.dependency_set.end(); d_it++){
	std::cout << *d_it;
      }
      std::cout << "\n";
      */
      /////////////////////////////////////////////////////////////////////////////////////

      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	  d_it != worknode.dependency_set.end(); d_it++){
        irep_idt renamed_id = *d_it;
        // detach the '@' symbol if there
        ssa_inliner.rename(renamed_id,
           ssa_depgraph.depnodes_map[worknode.node_index].rename_counter, false);
        renamed_dependencies.insert(renamed_id);
      }

      worknode.dependency_set = renamed_dependencies;

      if(!worknode.dependency_set.empty()){
	find_symbols_sett guard_dependencies;
	find_symbols(ssa_depgraph.depnodes_map[worknode.node_index].guard,
		     guard_dependencies);
	for(find_symbols_sett::const_iterator d_it = guard_dependencies.begin();
	    d_it != guard_dependencies.end(); d_it++){
	  worknode.dependency_set.insert(*d_it);
        }
      }

      /////////////////////////////////////////////////////////////////////////////////////
      /*
      std::cout << "\t size of dependency set: " << worknode.dependency_set.size() << "\n";

      std::cout << "\t dependency set: ";
      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	  d_it != worknode.dependency_set.end(); d_it++){
	std::cout << *d_it;
      }
      std::cout << "\n";
      */
      /////////////////////////////////////////////////////////////////////////////////////

      worknode.dependency_set = 
	compute_summary_rec(fname,worknode.dependency_set,
			    ssa_depgraph.depnodes_map[worknode.node_index].rename_counter,summaryt::call_sitet(ssa_depgraph.depnodes_map[worknode.node_index].location));
      slice.push_back(ssa_depgraph.depnodes_map[worknode.node_index].node_info);

      renamed_dependencies.clear();

      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
	  d_it != worknode.dependency_set.end(); d_it++){
        irep_idt renamed_id = *d_it;
        // detach the '@' symbol if there
        ssa_inliner.rename(renamed_id,
           ssa_depgraph.depnodes_map[worknode.node_index].rename_counter, false);
        renamed_dependencies.insert(renamed_id);
      }

      worknode.dependency_set = renamed_dependencies;

      if(!worknode.dependency_set.empty()){
	find_symbols_sett guard_dependencies;
	find_symbols(ssa_depgraph.depnodes_map[worknode.node_index].guard, guard_dependencies);
	for(find_symbols_sett::const_iterator d_it = guard_dependencies.begin();
	  d_it != guard_dependencies.end(); d_it++){
	  worknode.dependency_set.insert(*d_it);
        }
      }

    }

    // if the dependency set is non-empty
    if(!worknode.dependency_set.empty()){
      exprt worknode_info = ssa_depgraph.depnodes_map[worknode.node_index].node_info;
      if(ssa_depgraph.depnodes_map[worknode.node_index].is_assertion == true)
	worknode_info = not_exprt(worknode_info);
      
      if(worknode.node_index != 0){
	if(!(ssa_depgraph.depnodes_map[worknode.node_index].is_function_call)){
	  if((ssa_depgraph.depnodes_map[worknode.node_index].is_assertion == false) ||
	     (worknode_info == error_assertion)){
	    /*
	    std::cout << "Solver <-- " << function_name << ": (node) node#:"
		      << worknode.node_index << "\t original info ~ "
		      << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
	    */
            slice.push_back(worknode_info);
	    ssa_inliner.rename(worknode_info, counter);
#if 0
	    std::cout << "Solver <-- renamed assertion: " << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
	    std::cout << "Solver <-- " << function_name << ": (node) node#:"
		      << worknode.node_index << "\t  renamed info ~ "
		      << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
#endif
	    solver << worknode_info;
	  }
	}
	else{
	  exprt guard_binding = ssa_depgraph.depnodes_map[worknode.node_index].guard;
	  /*
	  std::cout << "Solver <-- " << function_name << ": (bind) node#:"
		    << worknode.node_index << "\t original info ~ "
		    << from_expr(ssa_db.get(function_name).ns, "", guard_binding) << "\n";
	  */
	  ssa_inliner.rename(guard_binding, counter);
#if 0
	  std::cout << "Solver <-- " << function_name << ": (bind) node#:"
		    << worknode.node_index << "\t  renamed info ~ "
		    << from_expr(ssa_db.get(function_name).ns, "", guard_binding) << "\n";
#endif
	  solver << guard_binding;
          slice.push_back(guard_binding);
	}
      }
    }
    
    // if not a function call and the dependency set is non-empty
    if((ssa_depgraph.depnodes_map[worknode.node_index].is_function_call == false) &&
       (!worknode.dependency_set.empty())){

      exprt worknode_info = ssa_depgraph.depnodes_map[worknode.node_index].node_info;
      if(ssa_depgraph.depnodes_map[worknode.node_index].is_assertion == true)
	worknode_info = not_exprt(worknode_info);

      if((ssa_depgraph.depnodes_map[worknode.node_index].is_assertion == false) ||
	 (worknode_info == error_assertion)){
	worknode.dependency_set =
	  ssa_depgraph.depnodes_map[worknode.node_index].used_symbols;
      }
    }
    
    for(ssa_dependency_grapht::annotated_predecessorst::const_iterator
	  p_it = ssa_depgraph.depnodes_map[worknode.node_index].predecessors.begin();
	p_it != ssa_depgraph.depnodes_map[worknode.node_index].predecessors.end();
	p_it++){
      
      ssa_dependency_grapht::annotated_predecessort pred = *p_it;
      int pred_node_index = pred.predecessor_node_index;
      find_symbols_sett pred_annotation = pred.annotation;

      bool dependencies_merged = false;
      for(worklistt::iterator w_it = work_waitlist.begin(); w_it != work_waitlist.end(); w_it++){
	if(w_it->node_index == pred_node_index){
	  
	  dependencies_merged = true;
	  
	  for(find_symbols_sett::const_iterator
		a_it=pred_annotation.begin(); a_it!=pred_annotation.end(); a_it++)
	    {
	      if(worknode.dependency_set.find(*a_it) != worknode.dependency_set.end()){
		if((w_it->dependency_set).find(*a_it) == (w_it->dependency_set).end()){
		  (w_it->dependency_set).insert(*a_it);
		}
	      }
	    }
	  break;
	}
      }
      
      if(dependencies_merged == false){
	worknodet new_worknode;
	new_worknode.node_index = pred_node_index;
	
	for(find_symbols_sett::const_iterator
	      a_it=pred_annotation.begin(); a_it!=pred_annotation.end(); a_it++)
	  {
	    if(worknode.dependency_set.find(*a_it) != worknode.dependency_set.end())
	      new_worknode.dependency_set.insert(*a_it);
	  }
	
	work_waitlist.push_back(new_worknode);
      }
    }

#if 0
    std::cout << function_name << ": worklist: ";
    for(worklistt::const_iterator w_it=worklist.begin();
	w_it != worklist.end(); w_it++){
      std::cout << w_it->node_index << " ";
    }
    std::cout << "\n";


    std::cout << "\t" << function_name << ": waitlist: ";
    for(worklistt::const_iterator w_it=work_waitlist.begin();
	w_it != work_waitlist.end(); w_it++){
      std::cout << w_it->node_index << " ";
    }
    std::cout << "\n";
#endif

    covered_nodes.push_back(worknode.node_index);
    worklist.pop_front();

#if 0
    std::cout << function_name << ": covered : ";
    for(int l = 0; l < covered_nodes.size(); l++){
      std::cout << covered_nodes[l] << " ";
    }
    std::cout << "\n";
#endif

    worklistt iterate_work_waitlist = work_waitlist;
    work_waitlist.clear();
    
    for(worklistt::const_iterator w_it = iterate_work_waitlist.begin(); w_it != iterate_work_waitlist.end(); w_it++){
      worknodet waitlisted_worknode = *w_it;

      bool uncovered_successor = false;
      
      std::vector<int> &waitlisted_worknode_successors =
	ssa_depgraph.depnodes_map[waitlisted_worknode.node_index].successors;
      
      for(unsigned i = 0; i < waitlisted_worknode_successors.size(); i++){
	bool check_covered = false;
	for(unsigned j = 0; j < covered_nodes.size(); j++){
	  if(waitlisted_worknode_successors[i] == covered_nodes[j]){
	    check_covered = true;
	    break;
	  }
	}
	if(!check_covered){
#if 0
	  std::cout << function_name << ": an uncovered successor of " << waitlisted_worknode.node_index << " : "
		    << waitlisted_worknode_successors[i] << "\n";
#endif
	  uncovered_successor = true;
	  break;
	}
      }
      
      if(!uncovered_successor){
	worklist.push_back(waitlisted_worknode);
      }
      else{
	work_waitlist.push_back(waitlisted_worknode);
      }

    }
  }
  
  /* the following code is to stop a warning; this function must
     return from the first if-condition inside the while loop */
  std::cout << "check graph of the function: " << function_name << "\n";
  assert(false);
  return dependency_set;
}

/*******************************************************************\

Function: summarizer_bw_cex_wpt::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

find_symbols_sett summarizer_bw_cex_wpt::compute_summary_rec
  (
   const function_namet &function_name,
   const find_symbols_sett &dependency_set,
   int counter,
   const summaryt::call_sitet &call_site)
{
  local_SSAt &SSA = ssa_db.get(function_name);
  summaryt summary;
  if(summary_db.exists(function_name))
    summary = summary_db.get(function_name);
  else
  {
    summary.params = SSA.params;
    summary.globals_in = SSA.globals_in;
    summary.globals_out = SSA.globals_out;
  }
  // recursively compute summaries for function calls
  find_symbols_sett new_dependency_set = 
    inline_summaries(function_name,dependency_set,counter,
		     summary.error_summaries[call_site]);

  summary_db.set(function_name,summary);

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out,SSA.ns);   
    debug() << out.str() << eom;
  }

  return new_dependency_set;
}

/*******************************************************************\

Function: summarizer_bw_cex_wpt::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_wpt::check()
{
  solver_calls++; // for statistics
  if(solver() == decision_proceduret::D_SATISFIABLE){
    //std::cout << "Solver <-- renamed info ~ SAT\n"; 
    return property_checkert::FAIL;
  }
  //std::cout << "Solver <-- renamed info ~ UNSAT\n"; 
  return property_checkert::UNKNOWN;
}

/*******************************************************************\

Function: summarizer_bw_cex_wpt::debug_print()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_wpt::debug_print
(
 const function_namet &function_name,
 find_symbols_sett &dependency_set)
{
  std::cout << "DebugInfo: function -> " << function_name
	    << " ; dependency_set -> ";
  for(find_symbols_sett::iterator d_it = dependency_set.begin();
      d_it != dependency_set.end(); d_it++){
    std::cout << *d_it << ", ";
  }
  std::cout << "\n";
}

/*******************************************************************\

Function: summarizer_bw_cex_wpt::simplify_summary()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/
void summarizer_bw_cex_wpt::simplify_summary_build_map(
  replace_mapt &replace_map, const exprt &expr)
{
  if(expr.id()==ID_equal)
  {
    replace_map[expr.op0()] = expr.op1();
    return;
  }
  forall_operands(it, expr)
    simplify_summary_build_map(replace_map, *it);
}
bool summarizer_bw_cex_wpt::simplify_summary_replace(
  const replace_mapt &replace_map, exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    bool result = true;
    exprt::operandst &args = to_function_application_expr(expr).arguments();
    for(size_t i=0;i<args.size();++i)
      result = replace_expr(replace_map, args[i]) && result;
    return result;
  }
  if(expr.id()==ID_equal)
  {
    return replace_expr(replace_map, expr.op1());
  }
  bool result = true;
  Forall_operands(it, expr)
    result = simplify_summary_replace(replace_map, *it) && result;
  return result;
}
void summarizer_bw_cex_wpt::simplify_summary_cleanup(
  const find_symbols_sett &vars, exprt &expr)
{
  if(expr.id()==ID_equal)
  {
    if(expr.op0().id()==ID_symbol &&
       vars.find(expr.op0().get(ID_identifier)) == vars.end())
      expr = true_exprt();
    return;
  }
  Forall_operands(it, expr)
    simplify_summary_cleanup(vars, *it);
}
exprt summarizer_bw_cex_wpt::simplify_summary(const namespacet &ns,
					      exprt summary,
					      const find_symbols_sett &vars)
{
#if 1
  std::cout << "INITIAL SUMMARY: " << from_expr(ns, "", summary) << std::endl;
#endif
  //build replace map
  replace_mapt replace_map;
  simplify_summary_build_map(replace_map, summary);

  while(!simplify_summary_replace(replace_map, summary));

#if 0
  std::cout << "PROJECTED SUMMARY: " << from_expr(ns, "", summary) << std::endl;
#endif
  simplify_summary_cleanup(vars, summary);

#if 0
  std::cout << "CLEANED UP SUMMARY: " << from_expr(ns, "", summary) << std::endl;
#endif
  summary = simplify_expr(summary, ns);

#if 0
  std::cout << "SIMPLIFIED SUMMARY: " << from_expr(ns, "", summary) << std::endl;
#endif
  return summary;
}
