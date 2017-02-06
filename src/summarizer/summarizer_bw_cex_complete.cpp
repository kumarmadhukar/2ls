/*******************************************************************\

Module: Simple Complete Counterexample-based Backward Analysis 

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

#include "summarizer_bw_cex_complete.h"

#define REFINE_ALL

/*******************************************************************\

Function: summarizer_bw_cex_completet::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_completet::summarize
(
  const function_namet &entry_function)
{
  // no dependencies to begin with
  find_symbols_sett dependency_set;

  status() << "\nSummarizing function " << entry_function << eom;
  compute_summary_rec(entry_function,dependency_set,-1);
}

/*******************************************************************\

Function: summarizer_bw_cex_completet::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_completet::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis (complete)..." << eom;
  error_assertion = _error_assertion;
  ssa_inliner.rename(error_assertion,-1,false);
  /*
    std::cout << "error assertion: "
    << from_expr(ssa_db.get(entry_function).ns, "", error_assertion)
    << "\n";
  */
  summarize(entry_function);
}


/*******************************************************************\

Function: summarizer_bw_cex_completet::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

find_symbols_sett summarizer_bw_cex_completet::inline_summaries
(
  const function_namet &function_name,
  find_symbols_sett &dependency_set,
  int counter)
{
  local_SSAt &SSA = ssa_db.get(function_name);
  ssa_local_unwindert &ssa_local_unwinder = ssa_unwinder.get(function_name);
  ssa_local_unwinder.compute_loop_continuation_conditions();
  //add enabling expressions
  exprt enable_exprs = SSA.get_enabling_exprs();
  ssa_inliner.rename(enable_exprs, counter);

  solver << enable_exprs;

  // assumptions must hold
  for(local_SSAt::nodest::const_iterator 
	n_it = SSA.nodes.begin(); n_it != SSA.nodes.end(); ++n_it)
    for(local_SSAt::nodet::assumptionst::const_iterator 
	  a_it = n_it->assumptions.begin(); a_it != n_it->assumptions.end(); ++a_it)
    {
      exprt assumption = *a_it;
      ssa_inliner.rename(assumption, counter);
      solver << assumption;
    }

#ifdef REFINE_ALL
  //TODO: let's just put all loops into the reason
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); ++n_it)
    if (n_it->loophead != SSA.nodes.end())
      reason[function_name].loops.insert(n_it->loophead->location);
#endif

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
    const ssa_dependency_grapht::depnodet &depnode = 
      ssa_depgraph.depnodes_map[worknode.node_index];
    
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
      return worknode.dependency_set;
    
    // modify worknode_dependency_set if the node is an assertion
    if(depnode.is_assertion == true){

      //std::cout << "\t\t an assertion node\n";
      for(find_symbols_sett::const_iterator d_it = depnode.used_symbols.begin();
          d_it != depnode.used_symbols.end(); d_it++){
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
    if(depnode.is_function_call == true){
      //std::cout << "fcall: working node: " << function_name << ": " << worknode.node_index << "\n";
      irep_idt fname = 
        to_symbol_expr((to_function_application_expr(depnode.node_info)).function()).get_identifier();
     
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
           depnode.rename_counter, false);
        renamed_dependencies.insert(renamed_id);
      }

      worknode.dependency_set = renamed_dependencies;

      if(!worknode.dependency_set.empty()){
        find_symbols_sett guard_dependencies;
        find_symbols(depnode.guard,
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

#ifdef REFINE_ALL
      //TODO: just put all function calls into reason
      reason[function_name].functions.insert(depnode.location);
#endif

      //recurse
      worknode.dependency_set = 
        compute_summary_rec(fname,worknode.dependency_set,
                            depnode.rename_counter);


      renamed_dependencies.clear();

      for(find_symbols_sett::iterator d_it = worknode.dependency_set.begin();
          d_it != worknode.dependency_set.end(); d_it++){
        irep_idt renamed_id = *d_it;
        // attach the '@' symbol if not already there
        ssa_inliner.rename(renamed_id,
           depnode.rename_counter, true);
        renamed_dependencies.insert(renamed_id);
      }

      worknode.dependency_set = renamed_dependencies;

      if(!worknode.dependency_set.empty()){
        find_symbols_sett guard_dependencies;
        find_symbols(depnode.guard, guard_dependencies);
        for(find_symbols_sett::const_iterator d_it = guard_dependencies.begin();
            d_it != guard_dependencies.end(); d_it++){
          worknode.dependency_set.insert(*d_it);
        }
      }

    }

    // if the dependency set is non-empty
    if(!worknode.dependency_set.empty())
    {
      exprt worknode_info = depnode.node_info;

      bool is_error_assertion = false;
      if(depnode.is_assertion)
      {
#if 0
        std::cout << "assertion: " << from_expr(SSA.ns, "", error_assertion) << std::endl;
        std::cout << "to check: " << from_expr(SSA.ns, "", worknode_info) << std::endl;
#endif
        assert(error_assertion.id()==ID_not);
        if(error_assertion.op0().id()!=ID_and)
          is_error_assertion = (worknode_info == error_assertion.op0());
        else
          forall_operands(a_it, error_assertion.op0())
            if(worknode_info == *a_it)
            {
              is_error_assertion = true;
              break;
            }
      }
      
      if(worknode.node_index != 0){
        if(!(depnode.is_function_call)){
          if(!depnode.is_assertion || is_error_assertion) 
          {
            /*
              std::cout << "Solver <-- " << function_name << ": (node) node#:"
              << worknode.node_index << "\t original info ~ "
              << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
            */
            ssa_inliner.rename(worknode_info, counter);
#if 0
            std::cout << "Solver <-- renamed assertion: " << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
            std::cout << "Solver <-- " << function_name << ": (node) node#:"
                      << worknode.node_index << "\t  renamed info ~ "
                      << from_expr((ssa_db.get(function_name)).ns, "", worknode_info) << "\n";
#endif

            if(depnode.is_assertion) //keep for later
              renamed_error_assertion.push_back(worknode_info);
            else
              solver << worknode_info;

            if(depnode.is_loop)
            {
              //loop head selects
              exprt lsguard = depnode.guard;
              ssa_inliner.rename(lsguard, counter);
              loophead_selects.push_back(lsguard);
              //solver.solver->set_frozen(solver.convert(lsguard));
              add_reason_to_check(lsguard,function_name,false,depnode.location);

              //loop continuations
              exprt::operandst local_loop_continues;
              get_loop_continues(SSA, ssa_local_unwinder, depnode.location, 
                                 local_loop_continues);
              for(size_t i=0; i<local_loop_continues.size(); ++i)
                ssa_inliner.rename(local_loop_continues[i], counter);
              loop_continues.insert(loop_continues.end(),
                                    local_loop_continues.begin(),
                                    local_loop_continues.end());
            }

          }
        }
        else{
          exprt guard_binding = depnode.guard;
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

#ifdef REFINE_ALL
          solver << guard_binding;
#else
          add_reason_to_check(guard_binding,function_name,true,depnode.location);
#endif
        }
      }
    }
    
    // if not a function call and the dependency set is non-empty
    if((depnode.is_function_call == false) &&
       (!worknode.dependency_set.empty())){

      exprt worknode_info = depnode.node_info;
      if(depnode.is_assertion == true)
        worknode_info = not_exprt(worknode_info);

      if((depnode.is_assertion == false) ||
         (worknode_info == error_assertion)){
        worknode.dependency_set =
          depnode.used_symbols;
      }
    }
    
    for(ssa_dependency_grapht::annotated_predecessorst::const_iterator
          p_it = depnode.predecessors.begin();
        p_it != depnode.predecessors.end();
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

Function: summarizer_bw_cex_completet::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

find_symbols_sett summarizer_bw_cex_completet::compute_summary_rec
(
  const function_namet &function_name,
  find_symbols_sett &dependency_set,
  int counter)
{
  // recursively compute summaries for function calls
  return inline_summaries(function_name,dependency_set,counter);
}

/*******************************************************************\

Function: summarizer_bw_cex_completet::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_completet::check()
{
  assert(!renamed_error_assertion.empty()); //otherwise the error assertion was not renamed

//add loophead selects
#ifdef REFINE_ALL
  solver.new_context();
  solver << not_exprt(conjunction(renamed_error_assertion));
  solver << conjunction(loophead_selects);
#else
  formula.push_back(solver.solver->convert(
                      not_exprt(conjunction(renamed_error_assertion))));
  solver.solver->set_assumptions(formula);
#endif

  solver_calls++; // for statistics
  if(solver() == decision_proceduret::D_SATISFIABLE)
  {
    //pop_context() not necessary
    return property_checkert::FAIL;
  }
#ifndef REFINE_ALL
  else
  {
    const namespacet &ns = ssa_db.get(entry_function).ns;
    //get reasons for spuriousness
    for(unsigned i=0; i<formula_expr.size(); i++) 
    {
      if(solver.solver->is_in_conflict(formula[i]))
      {
        debug() << "is_in_conflict: " << from_expr(ns, "", formula_expr[i]) << eom;
        const reason_to_checkt &r = reasons_to_check[i];
        if(r.is_function)
          reason[r.function_name].functions.insert(r.info);
        else
          reason[r.function_name].loops.insert(r.info);
      }
    }
    bvt assumptions;
    solver.solver->set_assumptions(assumptions);
    for(unsigned i=0; i<formula_expr.size(); i++) 
    {
      if(reasons_to_check[i].is_function)
        solver << literal_exprt(formula[i]);
    }
  }
#else
  solver.pop_context();
#endif    

  //check whether loops have been fully unwound
  bool fully_unwound = 
    is_fully_unwound(loop_continues,loophead_selects,solver);
  status() << "Loops " << (fully_unwound ? "" : "not ") 
           << "fully unwound" << eom;

  if(fully_unwound)
    return property_checkert::PASS;

  return property_checkert::UNKNOWN;
}

/*******************************************************************\

Function: summarizer_bw_cex_completet::debug_print()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_completet::debug_print
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

Function: summarizer_bw_cex_completet::add_reason_to_check

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_completet::add_reason_to_check(
  const exprt &expr,
  const function_namet &function_name,
  bool is_function, 
  const local_SSAt::locationt & info) 
{
  literalt l = solver.solver->convert(expr);
  if(l.is_false())
  {
    literalt dummy = solver.solver->convert(symbol_exprt("goto_symex::\\dummy", 
                                                         bool_typet()));
    formula.push_back(dummy);
    formula.push_back(!dummy);
  }
  else if(!l.is_true()) 
  {
    formula.push_back(l);
    formula_expr.push_back(expr);
    reasons_to_check.push_back(reason_to_checkt());
    reason_to_checkt &r = reasons_to_check.back();
    r.function_name = function_name;
    r.info = info;
    r.is_function = is_function;
  }
}
