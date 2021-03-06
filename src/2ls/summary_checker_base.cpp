/*******************************************************************\

Module: Summarizer Checker Base

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/options.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/language_util.h>
#include <util/prefix.h>
#include <goto-programs/write_goto_binary.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/prop/literal_expr.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_build_goto_trace.h"
#include "../domains/ssa_analyzer.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/ssa_const_propagator.h"
#include <cstdlib>

#include "show.h"
#include "instrument_goto.h"

#include "summary_checker_base.h"
#include "summarizer_bw_cex.h"
#include "summarizer_bw_cex_concrete.h"
#include "summarizer_bw_cex_ai.h"
#include "summarizer_bw_cex_complete.h"
#include "summarizer_bw_cex_wp.h"
#include "summarizer_bw_cex_all.h"

#include "../solver/summarizer_fw.h"
#include "../solver/summarizer_fw_term.h"
#include "../solver/summarizer_bw.h"
#include "../solver/summarizer_bw_term.h"

#ifdef SHOW_CALLING_CONTEXTS
#include "summarizer_fw_contexts.h"
#endif


/*******************************************************************\

Function: summary_checker_baset::SSA_dependency_graphs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::SSA_dependency_graphs(
  const goto_modelt &goto_model,  
  const namespacet &ns)
{
  // compute dependency graph for all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available()) continue;
    if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
	  
    status() << "Computing dependency graph of " << f_it->first << messaget::eom;
	  
    //ssa_db.depgraph_create(f_it->first, ns, ssa_inliner);
	  
    if(entry_function == f_it->first)
      ssa_db.depgraph_create(f_it->first, ns, ssa_inliner, true);
    else
      ssa_db.depgraph_create(f_it->first, ns, ssa_inliner, false); // change to true if all functions are to be treated equal

#if 0
    ssa_dependency_grapht &ssa_depgraph = ssa_db.get_depgraph(f_it->first);
    ssa_depgraph.output(debug()); debug() << eom;
    std::cout << "output SSA for function: " << f_it->first << "\n";
    ssa_db.get(f_it->first).output_verbose(std::cout);
#endif
  }
}

/*******************************************************************\

Function: summary_checker_baset::SSA_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::SSA_functions(const goto_modelt &goto_model,  const namespacet &ns)
{  
  entry_function = goto_model.goto_functions.entry_point();

  // compute SSA for all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available()) continue;
    if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
    status() << "Computing SSA of " << f_it->first << messaget::eom;
    
    ssa_db.create(f_it->first, f_it->second, ns);
    local_SSAt &SSA = ssa_db.get(f_it->first);
    
    // simplify, if requested
    if(simplify)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }

    SSA.output(debug()); debug() << eom;
  }

  // properties
  initialize_property_map(goto_model.goto_functions);
}

/*******************************************************************\

Function: summary_checker_baset::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::summarize(const goto_modelt &goto_model, 
                                      bool forward,
                                      bool termination)
{    
  summarizer_baset *summarizer = NULL;

#ifdef SHOW_CALLING_CONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    summarizer = new summarizer_fw_contextst(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  else
#endif
  {
    if(forward && !termination)
      summarizer = new summarizer_fwt(
        options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
    if(forward && termination)
      summarizer = new summarizer_fw_termt(
        options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
    if(!forward && !termination)
      summarizer = new summarizer_bwt(
        options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
    if(!forward && termination)
      summarizer = new summarizer_bw_termt(
        options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  }
  assert(summarizer != NULL);

  summarizer->set_message_handler(get_message_handler());

  if(!options.get_bool_option("context-sensitive") &&
     options.get_bool_option("all-functions"))
    summarizer->summarize();
  else
    summarizer->summarize(goto_model.goto_functions.entry_point());

  //statistics
  solver_instances += summarizer->get_number_of_solver_instances();
  solver_calls += summarizer->get_number_of_solver_calls();
  summaries_used += summarizer->get_number_of_summaries_used();
  termargs_computed += summarizer->get_number_of_termargs_computed();

  delete summarizer;
}

/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs: function_name != nil
            checks all functions in the call graph from the entry point
          else 
            checks all functions 

 Outputs:

 Purpose:

\*******************************************************************/

summary_checker_baset::resultt summary_checker_baset::check_properties()
{
  std::set<irep_idt> seen_function_calls;
  return check_properties("", "", seen_function_calls, false);
}

summary_checker_baset::resultt summary_checker_baset::check_properties(
  irep_idt function_name, 
  irep_idt entry_function, 
  std::set<irep_idt> seen_function_calls,
  bool is_inlined)
{
  if(function_name!="")
  {
    ssa_dbt::functionst::const_iterator f_it = 
      ssa_db.functions().find(function_name);
    assert(f_it != ssa_db.functions().end());
    local_SSAt &SSA = *f_it->second;

    // call recursively for all function calls first
    for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
        n_it != SSA.nodes.end(); ++n_it)
    {
      for(local_SSAt::nodet::function_callst::const_iterator ff_it = 
            n_it->function_calls.begin();
          ff_it != n_it->function_calls.end(); ff_it++)
      {
        assert(ff_it->function().id()==ID_symbol); //no function pointers
        irep_idt fname = to_symbol_expr(ff_it->function()).get_identifier();
        
        //ENHANCE?: can the return value be exploited?
        if(ssa_db.functions().find(fname)!=ssa_db.functions().end() &&
           (!summary_db.exists(fname) ||	
            summary_db.get(fname).bw_transformer.is_nil()))
        {
#if 0
          debug() << "Checking call " << fname << messaget::eom;
#endif
          if(seen_function_calls.find(fname) == seen_function_calls.end()){
            seen_function_calls.insert(fname);
            check_properties(fname, entry_function, seen_function_calls,
              n_it->function_calls_inlined);
          }
        }
      }
    }

    if(!is_inlined)
    {
      //now check function itself
      status() << "Checking properties of " << f_it->first << messaget::eom;
      check_properties(f_it, entry_function);
    }
  }
  else // check all the functions
  {
    for(ssa_dbt::functionst::const_iterator f_it = ssa_db.functions().begin();
        f_it != ssa_db.functions().end(); f_it++)
    {
      status() << "Checking properties of " << f_it->first << messaget::eom;

#if 0
      //for debugging
      show_ssa_symbols(*f_it->second,std::cerr);
#endif

      check_properties(f_it);

      if(options.get_bool_option("show-invariants")) 
      {
        if(!summary_db.exists(f_it->first)) continue;
        show_invariants(*(f_it->second),summary_db.get(f_it->first),result());
        result() << eom;
      }
    }
  }

  summary_checker_baset::resultt result = property_checkert::PASS;
  if(function_name=="" || function_name==entry_function)
  {
    // determine overall status
    for(property_mapt::const_iterator
          p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
    {
      if(p_it->second.result==FAIL)
        return property_checkert::FAIL;
      if(p_it->second.result==UNKNOWN)
        result = property_checkert::UNKNOWN;
    }
  }
    
  return result;
}

/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summary_checker_baset::check_properties(
  const ssa_dbt::functionst::const_iterator f_it,
  irep_idt entry_function)
{
  unwindable_local_SSAt &SSA = *f_it->second;

  //check whether function has assertions
  if(!has_assertion(f_it->first))
    return;

  bool all_properties = options.get_bool_option("all-properties");
  bool build_error_trace = options.get_bool_option("show-trace");

  SSA.output(debug()); debug() << eom;
  
  // incremental version

  // solver
  incremental_solvert &solver = ssa_db.get_solver(f_it->first);
  solver.set_message_handler(get_message_handler());

#if 0
  // TEST ssa_const_propagation
  if(options.get_bool_option("ssa-propagation"))
  {
    ssa_const_propagatort ssa_const_propagator;
    std::list<exprt> c;
    ssa_const_propagator(c,SSA);
    solver << c;
    debug() << "SSA const propagation: " << eom;
    for(std::list<exprt>::iterator it = c.begin();
        it!=c.end(); it++)
      debug() << "  " << from_expr(SSA.ns,"",*it) << eom;
  }
#endif
  
  // give SSA to solver
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();

  exprt enabling_expr = SSA.get_enabling_exprs();
  solver << enabling_expr;

  // invariant, calling contexts
  if(summary_db.exists(f_it->first))
  {
    const summaryt &summary = summary_db.get(f_it->first);
    if(!summary.fw_invariant.is_nil())
      solver << summary.fw_invariant;
    if(!summary.fw_precondition.is_nil())
      solver << summary.fw_precondition;
  }

  //callee summaries and inlined functions
  ssa_inlinert::assertion_mapt assertion_map;
  solver << ssa_inliner.get_summaries(SSA, assertion_map);

  //spuriousness checkers
  summarizer_bw_cex_baset *summarizer_bw_cex = NULL;
  incremental_solvert* cex_complete_solver = 
    incremental_solvert::allocate(SSA.ns,
                                  options.get_bool_option("refine"));
#if 1
  cex_complete_solver->set_message_handler(get_message_handler());
#endif
  if(options.get_bool_option("inline") ||
     options.get_option("spurious-check") == "concrete")
  {
    summarizer_bw_cex = new summarizer_bw_cex_concretet(
      options,summary_db,ssa_db,
      ssa_unwinder,ssa_inliner,
      entry_function,f_it->first);
  }
  else if(options.get_option("spurious-check") == "abstract")
  {
    summarizer_bw_cex = new summarizer_bw_cex_ait(
      options,summary_db,ssa_db,
      ssa_unwinder,ssa_inliner,
      entry_function,f_it->first);
  }
  else if(options.get_option("spurious-check") == "complete")
  {
    summarizer_bw_cex = new summarizer_bw_cex_completet(
      options,summary_db,ssa_db,
      ssa_unwinder,ssa_inliner,*cex_complete_solver,
      entry_function,f_it->first);
  }
  else if(options.get_option("spurious-check") == "wp")
  {
    summarizer_bw_cex = new summarizer_bw_cex_wpt(
      options,summary_db,ssa_db,
      ssa_unwinder,ssa_inliner,*cex_complete_solver,
      entry_function,f_it->first);
  }
  else if(options.get_option("spurious-check") == "all")
  {
    summarizer_bw_cex = new summarizer_bw_cex_allt(
      options,summary_db,ssa_db,
      ssa_unwinder,ssa_inliner,*cex_complete_solver,
      entry_function,f_it->first);
  }
  assert(summarizer_bw_cex != NULL);
  summarizer_bw_cex->set_message_handler(get_message_handler());

  cover_goals_extt cover_goals(
    SSA, solver, property_map,
    all_properties, build_error_trace,
    *summarizer_bw_cex);

  for(ssa_inlinert::assertion_mapt::const_iterator
        aa_it=assertion_map.begin();
      aa_it!=assertion_map.end();
      aa_it++)
  {
    irep_idt property_id = aa_it->first->source_location.get_property_id();

    //do not recheck properties that have already been decided
    if(property_map[property_id].result!=UNKNOWN) 
      continue; 

#if 0
    if(property_id=="") //TODO: some properties do not show up in initialize_property_map
      continue;     
#endif

    for(exprt::operandst::const_iterator
          a_it=aa_it->second.begin();
        a_it!=aa_it->second.end();
        a_it++)
    {
      exprt property=*a_it;

      if(simplify)
        property=::simplify_expr(property, SSA.ns);

#if 1
      debug() << "property: " << from_expr(SSA.ns, "", property) << eom;
#endif
 
      property_map[property_id].location = aa_it->first;
      cover_goals.goal_map[property_id].conjuncts.push_back(property);
    }
  }
    
  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    //literalt p=!solver.convert(conjunction(it->second.conjuncts));
    //cover_goals.add(p);
    cover_goals.add(not_exprt(conjunction(it->second.conjuncts)));
  }
  
  status() << "Running " << solver.solver->decision_procedure_text() << eom;

  cover_goals();  
  /*
    std::cout << "Output Verbose: " << entry_function << "\n";
    (ssa_db.get(entry_function)).output_verbose(std::cout);
    assert(false);
  */
  //set all non-covered goals to PASS except if we do not try 
  //  to cover all goals and we have found a FAIL
  if(all_properties || cover_goals.number_covered()==0) 
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=
      cover_goals.goals.begin();
    for(cover_goals_extt::goal_mapt::const_iterator
          it=cover_goals.goal_map.begin();
        it!=cover_goals.goal_map.end();
        it++, g_it++)
    {
      if(!g_it->covered) property_map[it->first].result=PASS;
    }
  }

  solver.pop_context();

  summarizer_bw_cex->get_reason(reason);

  debug() << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;

  delete summarizer_bw_cex;
  delete cex_complete_solver;
} 

/*******************************************************************\

Function: summary_checker_baset::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::report_statistics()
{
  for(ssa_dbt::functionst::const_iterator f_it = ssa_db.functions().begin();
      f_it != ssa_db.functions().end(); f_it++)
  {
    incremental_solvert &solver = ssa_db.get_solver(f_it->first);
    unsigned calls = solver.get_number_of_solver_calls();
    if(calls>0) solver_instances++;
    solver_calls += calls;
  }
  statistics() << "** statistics: " << eom;
  statistics() << "  number of solver instances: " << solver_instances << eom;
  statistics() << "  number of solver calls: " << solver_calls << eom;
  statistics() << "  number of summaries used: " 
               << summaries_used << eom;
  statistics() << "  number of termination arguments computed: " 
               << termargs_computed << eom;
  statistics() << eom;
}
  
/*******************************************************************\

Function: summary_checker_baset::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::do_show_vcc(
  const local_SSAt &SSA,
  const goto_programt::const_targett i_it,
  const local_SSAt::nodet::assertionst::const_iterator &a_it)
{
  std::cout << i_it->source_location << "\n";
  std::cout << i_it->source_location.get_comment() << "\n";
  
  std::list<exprt> ssa_constraints;
  ssa_constraints << SSA;

  unsigned i=1;
  for(std::list<exprt>::const_iterator c_it=ssa_constraints.begin();
      c_it!=ssa_constraints.end();
      c_it++, i++)
    std::cout << "{-" << i << "} " << from_expr(SSA.ns, "", *c_it) << "\n";

  std::cout << "|--------------------------\n";
  
  std::cout << "{1} " << from_expr(SSA.ns, "", *a_it) << "\n";
  
  std::cout << "\n";
}

/*******************************************************************\

Function: summary_checker_baset::instrument_and_output

  Inputs:

 Outputs:

 Purpose: instruments the code with the inferred information
          and outputs it to a goto-binary

\*******************************************************************/

void summary_checker_baset::instrument_and_output(goto_modelt &goto_model)
{
  instrument_gotot instrument_goto(options,ssa_db,summary_db);
  instrument_goto(goto_model);
  std::string filename = options.get_option("instrument-output");
  status() << "Writing instrumented goto-binary " << filename << eom;
  write_goto_binary(filename, 
                    goto_model.symbol_table, 
                    goto_model.goto_functions, get_message_handler());
}

/*******************************************************************\

Function: summary_checker_baset::has_assertion

  Inputs:

 Outputs: 

 Purpose: searches recursively for assertions in inlined functions

\*******************************************************************/

bool summary_checker_baset::has_assertion(irep_idt function_name)
{
  //  SSA.goto_function.body.has_assertion() has become too semantic
  bool _has_assertion = false;
  const local_SSAt &SSA = ssa_db.get(function_name);

  for(local_SSAt::nodest::const_iterator 
	  n_it = SSA.nodes.begin(); n_it != SSA.nodes.end(); ++n_it)
  {
    for(local_SSAt::nodet::assertionst::const_iterator 
	    a_it = n_it->assertions.begin(); a_it != n_it->assertions.end(); ++a_it)
    {
      irep_idt property_id = n_it->location->source_location.get_property_id();
    
      if(n_it->location->guard.is_true())
        property_map[property_id].result=PASS;
      else
        _has_assertion=true;
    }
    if(!n_it->function_calls_inlined)
      continue;

    for(local_SSAt::nodet::function_callst::const_iterator 
	    f_it = n_it->function_calls.begin(); 
        f_it != n_it->function_calls.end(); ++f_it)
    {
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      if(ssa_db.functions().find(fname)==ssa_db.functions().end())
        continue;

      bool new_has_assertion = has_assertion(fname); //recurse
      _has_assertion = _has_assertion || new_has_assertion;
    }
  }

  return _has_assertion;
}
