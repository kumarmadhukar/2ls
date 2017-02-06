/*******************************************************************\

Module: Simple Counterexample-based Backward Analysis 

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

//#define OPT_11 // simplify before pushing to solver
#define OPT_12 // collect, conjunct, simplify and then push to the solver

//#define OPT_2  // a fresh solver each time

//TODO: a bug in the fresh solver case; does not compute
//calling contexts (see struct tests in regression)

//#define DEBUG

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_bw_cex_concrete.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

/*******************************************************************\

Function: summarizer_bw_cex_concretet::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_concretet::summarize(const function_namet &function_name)
{
  exprt postcondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  compute_summary_rec(function_name,summaryt::entry_call_site,
		      postcondition,true);
}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_concretet::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis (concrete)..." << eom;
  error_assertion = _error_assertion;

  summarize(entry_function);
}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_concretet::check()
{
  property_checkert::resultt result = property_checkert::FAIL;
  if(!summary_db.exists(entry_function))
  {
    result = property_checkert::UNKNOWN;
  }
  else
  {
    const summaryt &summary = summary_db.get(entry_function);
    if(summary.error_summaries.empty() ||
       summary.error_summaries.begin()->second.is_nil() ||
       summary.error_summaries.begin()->second.is_true())
      result = property_checkert::UNKNOWN;
  }

  //we are only complete if everything was inlined
  if(result == property_checkert::UNKNOWN &&
     options.get_bool_option("inline"))
  {
    incremental_solvert &solver = ssa_db.get_solver(entry_function);
    const local_SSAt &ssa = ssa_db.get(entry_function);
    ssa_local_unwindert &ssa_local_unwinder = 
      ssa_unwinder.get(entry_function);
    exprt::operandst loophead_selects;
    exprt::operandst loop_continues;
    get_loophead_selects(ssa, ssa_local_unwinder, 
                         *solver.solver, loophead_selects);
    get_loop_continues(ssa, ssa_local_unwinder, loop_continues);
    //check whether loops have been fully unwound
    bool fully_unwound = 
      is_fully_unwound(loop_continues,loophead_selects,solver);
    status() << "Loops " << (fully_unwound ? "" : "not ") 
             << "fully unwound" << eom;

    if(fully_unwound)
      result = property_checkert::PASS;
  }

  return result;
}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_concretet::compute_summary_rec(
  const function_namet &function_name,
  const summaryt::call_sitet &call_site,
  const exprt &_postcondition,
  bool context_sensitive)
{
  local_SSAt &SSA = ssa_db.get(function_name); 

  //TODO: let's just put all loops into the reason
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); ++n_it)
    if (n_it->loophead != SSA.nodes.end())
      reason[function_name].loops.insert(n_it->loophead->location);
  
  summaryt summary;
  if(summary_db.exists(function_name))
    summary = summary_db.get(function_name);
  else
  {
    summary.params = SSA.params;
    summary.globals_in = SSA.globals_in;
    summary.globals_out = SSA.globals_out;
    summary.nondets = SSA.nondets;
  }

    // insert assertion
  exprt end_guard = SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  exprt postcondition = implies_exprt(end_guard,_postcondition);
  if(function_name == error_function)
  {
    postcondition = and_exprt(postcondition,not_exprt(error_assertion));
  }
    
  summary.bw_postcondition = _postcondition;

#if 0
  debug() << "Postcondition: " << from_expr(SSA.ns, "", postcondition) << eom;
#endif
  
  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,summary,
		   postcondition,context_sensitive,
		   true); 

  status() << "Analyzing function "  << function_name << eom;

  do_summary(function_name,call_site,SSA,summary,summary,postcondition,context_sensitive);

  if(function_name == error_function)
    summary.has_assertion = true;

  summary_db.set(function_name,summary);

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out,SSA.ns);   
    debug() << out.str() << eom;
  }

}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::do_summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_concretet::do_summary(
  const function_namet &function_name, 
  const summaryt::call_sitet &call_site,
  local_SSAt &SSA,
  const summaryt &old_summary,
  summaryt &summary,
  const exprt &postcondition,
  bool context_sensitive)
{
  status() << "Computing error summary" << eom;

  // solver

#ifdef OPT_2
  incremental_solvert* fresh_solver = 
    incremental_solvert::allocate(SSA.ns, options.get_bool_option("refine"));
  incremental_solvert &solver = (*fresh_solver);
  SSA.unmark_nodes();
  exprt::operandst store;
#else
  incremental_solvert &solver = ssa_db.get_solver(function_name);
#endif
  
  solver.set_message_handler(get_message_handler());

  //ENHANCE: we could reuse the solver state, but it's difficult
  //   (the function maybe called several times)
  exprt::operandst c;

#ifdef OPT_12
  exprt::operandst store;
#endif

  //add forward information if available
  if(!old_summary.fw_precondition.is_nil())
    c.push_back(old_summary.fw_precondition);
  if(!old_summary.fw_invariant.is_nil())
    c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries

  exprt::operandst assert_postcond, noassert_postcond;
  // add error summaries for function calls
  bool assertion_flag;
  assertion_flag = ssa_inliner.get_summaries(SSA,call_site,false,assert_postcond,noassert_postcond,c); //backward summaries
  assert_postcond.push_back(postcondition);  //context

  //add nondet variables from callees to summary.nondets
  std::set<exprt> summary_vars;
  find_symbols(conjunction(assert_postcond),summary_vars);
  for(std::set<exprt>::const_iterator it = summary_vars.begin();
      it != summary_vars.end(); ++it)
    if(it->id()==ID_nondet_symbol)
      summary.nondets.insert(*it);

#ifdef DEBUG
  std::cout << "Assert Summary: " << from_expr(SSA.ns, "", conjunction(assert_postcond)) << "\n\n";
  std::cout << "Noassert Summary: " << from_expr(SSA.ns, "", conjunction(noassert_postcond)) << "\n\n";
#endif

  c.push_back(not_exprt(conjunction(assert_postcond))); 
  c.push_back(not_exprt(disjunction(noassert_postcond))); 

#ifdef DEBUG
  debug() << "Backward summaries: " << 
    from_expr(SSA.ns, "", simplify_expr(conjunction(c),SSA.ns)) << eom;
#endif

#ifdef OPT_12
  store << SSA;
#else
#ifdef OPT_2
  store << SSA;
#else
  solver << SSA;
#endif
#endif

#ifndef OPT_2  
  solver.new_context();
#endif

  // assumptions must hold
  for(local_SSAt::nodest::const_iterator 
	n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end();
      ++n_it)
    for(local_SSAt::nodet::assumptionst::const_iterator 
	  a_it = n_it->assumptions.begin(); 
	a_it != n_it->assumptions.end();
	++a_it)
    {

#ifdef OPT_11
      solver << simplify_expr(*a_it, SSA.ns);
#else
#ifdef OPT_12
      store.push_back(*a_it);
#else
#ifdef OPT_2
      store.push_back(*a_it);
#else
      solver << *a_it;
#endif
#endif
#endif

    }

#ifdef OPT_12
  store.push_back(SSA.get_enabling_exprs());
#else
#ifdef OPT_2
  store.push_back(SSA.get_enabling_exprs());
#else
  solver << SSA.get_enabling_exprs();
#endif
#endif

#ifdef OPT_11
  solver << simplify_expr(conjunction(c), SSA.ns);
#else
#ifdef OPT_12
  store.push_back(conjunction(c));
#else
#ifdef OPT_2
  store.push_back(conjunction(c));
#else
  solver << conjunction(c);
#endif
#endif
#endif
  
  exprt::operandst loophead_selects;
  get_loophead_selects(SSA,ssa_unwinder.get(function_name),*solver.solver,loophead_selects);
  
#ifdef OPT_11
  solver << simplify_expr(conjunction(loophead_selects), SSA.ns);
#else
#ifdef OPT_12
  store.push_back(conjunction(loophead_selects));
#else
#ifdef OPT_2
  store.push_back(conjunction(loophead_selects));
#else
  solver << conjunction(loophead_selects);
#endif
#endif
#endif

#ifdef OPT_12
#ifdef DEBUG
  std::cout << "\n\n\n pushing to the solver in do_summary:" << from_expr(SSA.ns, "", conjunction(store)) << "\n\n\n";
#endif
  solver << simplify_expr(conjunction(store), SSA.ns);
#endif
#ifdef OPT_2
#ifdef DEBUG
  std::cout << "\n\n\n pushing to the solver in do_summary:" << from_expr(SSA.ns, "", simplify_expr(conjunction(store), SSA.ns)) << "\n\n\n";
#endif
  solver << simplify_expr(conjunction(store), SSA.ns);
#endif

  //statistics
  solver_calls++;

  //solve
  if(solver() == decision_proceduret::D_UNSATISFIABLE)
  {
    summary.error_summaries[call_site] = true_exprt(); //TODO: this is likely to be incomplete
    summary.has_assertion = assertion_flag;
#ifndef OPT_2  
    solver.pop_context();
#endif

    return;
  }
 
  //build error summary and add to summary
  exprt::operandst var_values;

  for(local_SSAt::var_listt::const_iterator it = SSA.params.begin();
      it != SSA.params.end(); it++){
    exprt summ_value = solver.get(*it);
    if(!summ_value.is_nil())
      var_values.push_back(equal_exprt(*it, summ_value));
  }

  for(local_SSAt::var_sett::const_iterator it = SSA.globals_in.begin();
      it != SSA.globals_in.end(); it++){
    exprt summ_value = solver.get(*it);
    if(!summ_value.is_nil())
      var_values.push_back(equal_exprt(*it, summ_value));
  }

  for(local_SSAt::var_sett::const_iterator it = SSA.globals_out.begin();
      it != SSA.globals_out.end(); it++){
    exprt summ_value = solver.get(*it);
    if(!summ_value.is_nil())
      var_values.push_back(equal_exprt(*it, summ_value));
  }

  for(std::set<exprt>::const_iterator it = summary.nondets.begin();
      it != summary.nondets.end(); it++){
    exprt summ_value = solver.get(*it);
    if(!summ_value.is_nil())
      var_values.push_back(equal_exprt(*it, summ_value));
  }

  summary.error_summaries[call_site] = not_exprt(conjunction(var_values));
  summary.has_assertion = assertion_flag;

#ifndef OPT_2  
  solver.pop_context();
#endif

#ifdef OPT_2
  delete fresh_solver;
#endif

}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_concretet::inline_summaries(
  const function_namet &function_name, 
  local_SSAt &SSA, 
  const summaryt &old_summary,
  const exprt &postcondition,
  bool context_sensitive,
  bool sufficient)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.end();
      n_it != SSA.nodes.begin(); )
  {
    n_it--;

    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      
      exprt postcondition_call =  true_exprt();
      postcondition_call = compute_calling_context2(
      	function_name,SSA,old_summary,n_it,f_it,postcondition,sufficient);

      //TODO: just put all function calls into reason
      reason[function_name].functions.insert(n_it->location);

      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      status() << "Recursively summarizing function " << fname << eom;
      compute_summary_rec(fname,summaryt::call_sitet(n_it->location), 
			  postcondition_call,context_sensitive);
    }
  }
}

/*******************************************************************\

Function: summarizer_bw_cex_concretet::compute_calling_context2()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt summarizer_bw_cex_concretet::compute_calling_context2(  
  const function_namet &function_name, 
  local_SSAt &SSA,
  summaryt old_summary,
  local_SSAt::nodest::const_iterator n_it, 
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &postcondition,
  bool sufficient)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  // solver

#ifdef OPT_2
  incremental_solvert* fresh_solver = 
    incremental_solvert::allocate(SSA.ns, options.get_bool_option("refine"));
  incremental_solvert &solver = (*fresh_solver);
#else
  incremental_solvert &solver = ssa_db.get_solver(function_name);
#endif

  solver.set_message_handler(get_message_handler());

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::const_iterator, local_SSAt::var_sett>
    cs_globals_out;
  SSA.get_globals(n_it->location,cs_globals_out[f_it],false);

  exprt::operandst c;

#ifdef OPT_12
  exprt::operandst store;
#endif
  
  // add forward information if available
  if(!old_summary.fw_precondition.is_nil())
      c.push_back(old_summary.fw_precondition);
  if(!old_summary.fw_invariant.is_nil())
      c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries

  exprt::operandst assert_postcond, noassert_postcond;
  // add error summaries for function calls
  ssa_inliner.get_summaries(SSA,summaryt::call_sitet(n_it->location),false,assert_postcond,noassert_postcond,c); //backward summaries
  assert_postcond.push_back(postcondition);  //context
  c.push_back(not_exprt(conjunction(assert_postcond))); 
  c.push_back(not_exprt(disjunction(noassert_postcond))); 

#ifdef OPT_12
  store << SSA;
#else
  solver << SSA;
#endif
  
  solver.new_context();

#ifdef OPT_12
  store.push_back(SSA.get_enabling_exprs());
#else
  solver << SSA.get_enabling_exprs();
#endif

#ifdef OPT_11
  solver << simplify_expr(conjunction(c), SSA.ns);
#else
#ifdef OPT_12
  store.push_back(conjunction(c));
#else
  solver << conjunction(c);
#endif
#endif
  
  exprt::operandst loophead_selects;
  get_loophead_selects(SSA,ssa_unwinder.get(function_name),*solver.solver,loophead_selects);

#ifdef OPT_11
  solver << simplify_expr(conjunction(loophead_selects), SSA.ns);
#else
#ifdef OPT_12
  store.push_back(conjunction(loophead_selects));
#else
  solver << conjunction(loophead_selects);
#endif
#endif
    
#ifdef OPT_12
#ifdef DEBUG
  std::cout << "\n\n\n pushing to the solver in compute_calling_context2:" << from_expr(SSA.ns, "", conjunction(store)) << "\n\n\n";
#endif
  solver << simplify_expr(conjunction(store), SSA.ns);
#endif
  
  
  // build postcondition
  exprt postcondition_call;
  
  if(solver() != decision_proceduret::D_SATISFIABLE)
  {
    postcondition_call = true_exprt(); //TODO: this is likely to be incomplete
    solver.pop_context();
    return postcondition_call;
  }

  bool result = solver()==decision_proceduret::D_SATISFIABLE;
  assert(result);
 
  exprt::operandst postcond_values; 
  for(local_SSAt::var_sett::const_iterator it = cs_globals_out[f_it].begin();
      it != cs_globals_out[f_it].end(); it++)
  {
    exprt postc_value = solver.get(*it);
    postcond_values.push_back(equal_exprt(*it, postc_value));
  }
  postcondition_call = conjunction(postcond_values);

  solver.pop_context();

  // get callee SSA and rename
  local_SSAt &fSSA = ssa_db.get(fname); 
  ssa_inliner.rename_to_callee(f_it, fSSA.params,
			     cs_globals_out[f_it],fSSA.globals_out,
			     postcondition_call);

  debug() << "Backward calling context for " << 
    from_expr(SSA.ns, "", *f_it) << ": " 
	  << from_expr(SSA.ns, "", postcondition_call) << eom;

  //statistics
  solver_calls++;

#ifdef OPT_2
  delete fresh_solver;
#endif

  return not_exprt(postcondition_call);
}
 

