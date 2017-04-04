/*******************************************************************\

Module: Summarizer Base

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_base.h"
#include "summary_db.h"

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_summary.h>
#include <domains/template_generator_callingcontext.h>

#include <ssa/local_ssa.h>
#include <ssa/simplify_ssa.h>


/*******************************************************************\

Function: summarizer_baset::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_baset::summarize()
{
  exprt precondition=true_exprt(); // initial calling context
  for(functionst::const_iterator it=ssa_db.functions().begin();
      it!=ssa_db.functions().end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first) ||
       summary_db.get(it->first).mark_recompute)
      compute_summary_rec(it->first, precondition, false);
    else
      status() << "Summary for function " << it->first
               << " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizer_baset::summarize

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizer_baset::summarize(const function_namet &function_name)
{
  exprt precondition=true_exprt(); // initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name) ||
     summary_db.get(function_name).mark_recompute)
  {
    compute_summary_rec(
      function_name,
      precondition,
      options.get_bool_option("context-sensitive"));
  }
  else
    status() << "Summary for function " << function_name
             << " exists already" << eom;
}

/*******************************************************************\

Function: summarizer_baset::check_call_reachable

  Inputs:

 Outputs:

 Purpose: returns false if function call is not reachable

\*******************************************************************/

bool summarizer_baset::check_call_reachable(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt& precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  debug() << "Checking reachability of call to " << fname << eom;

  bool reachable=false;

  // reachability check
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << precondition;
  solver << ssa_inliner.get_summaries(SSA);

  symbol_exprt guard=SSA.guard_symbol(n_it->location);
  ssa_unwinder.get(function_name).unwinder_rename(guard, *n_it, false);
  solver << guard;

#if 0
  std::cout << "guard: " << from_expr(SSA.ns, "", guard) << std::endl;
  std::cout << "enable: " << from_expr(SSA.ns, "", SSA.get_enabling_exprs())
            << std::endl;
  std::cout << "precondition: " << from_expr(SSA.ns, "", precondition)
            << std::endl;
  std::cout << "summaries: "
            << from_expr(SSA.ns, "", ssa_inliner.get_summaries(SSA))
            << std::endl;
#endif

  if(!forward)
    solver << SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
  {
    reachable=true;
    debug() << "Call is reachable" << eom;
    break;
  }
  case decision_proceduret::D_UNSATISFIABLE:
  {
    debug() << "Call is not reachable" << eom;
    break;
  }
  default: assert(false); break;
  }

  solver.pop_context();

  return reachable;
}

/*******************************************************************\

Function: summarizer_baset::compute_calling_context

  Inputs:

 Outputs:

 Purpose: computes callee preconditions from the calling context
          for a single function call

\*******************************************************************/

exprt summarizer_baset::compute_calling_context(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << ssa_inliner.get_summaries(SSA);

  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_callingcontextt template_generator(
    options, ssa_db, ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(), SSA, n_it, f_it, forward);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::const_iterator,
           local_SSAt::var_sett>
    cs_globals_in;
  if(forward)
    SSA.get_globals(n_it->location, cs_globals_in[f_it]);
  else
    SSA.get_globals(n_it->location, cs_globals_in[f_it], false);

  exprt cond=precondition;
  if(!forward)
    cond=and_exprt(
      cond, SSA.guard_symbol(--SSA.goto_function.body.instructions.end()));

  // analyze
  analyzer(solver, SSA, cond, template_generator);

  // set preconditions
  local_SSAt &fSSA=ssa_db.get(fname);

  preconditiont precondition_call;
  analyzer.get_result(
    precondition_call,
    template_generator.callingcontext_vars());
  ssa_inliner.rename_to_callee(
    f_it, fSSA.params, cs_globals_in[f_it], fSSA.globals_in, precondition_call);

  debug() << (forward ? "Forward " : "Backward ") << "calling context for "
          << from_expr(SSA.ns, "", *f_it) << ": "
          << from_expr(SSA.ns, "", precondition_call) << eom;

  // statistics
  solver_instances+=analyzer.get_number_of_solver_instances();
  solver_calls+=analyzer.get_number_of_solver_calls();

  solver.pop_context();

  return precondition_call;
}

/*******************************************************************\

Function: summarizer_baset::get_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_baset::get_assertions(
  const local_SSAt &SSA,
  exprt::operandst &assertions)
{
  for(const auto &node : SSA.nodes)
    for(const auto &a : node.assertions)
      assertions.push_back(a);
}

/*******************************************************************\

Function: summarizer_baset::check_precondition

  Inputs:

 Outputs:

 Purpose: returns false if the summary needs to be recomputed

\*******************************************************************/

bool summarizer_baset::check_precondition(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &precondition,
  bool context_sensitive)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds=false;
  exprt assertion;

  if(summary_db.exists(fname))
  {
    summaryt summary=summary_db.get(fname);
    if(summary.mark_recompute)
      return false;
    if(!context_sensitive ||
       summary.fw_precondition.is_true())  // precondition trivially holds
    {
      status() << "Precondition trivially holds, replacing by summary."
               << eom;
      summaries_used++;
      precondition_holds=true;
    }
    else
    {
      assertion=summary.fw_precondition;

      // getting globals at call site
      local_SSAt::var_sett cs_globals_in;
      SSA.get_globals(n_it->location, cs_globals_in);

      ssa_inliner.rename_to_caller(
        f_it, summary.params, cs_globals_in, summary.globals_in, assertion);

      debug() << "precondition assertion: "
              << from_expr(SSA.ns, "", assertion) << eom;

      precondition_holds=false;
    }
  }
  else if(!ssa_db.exists(fname))
  {
    status() << "Function " << fname << " not found" << eom;
    precondition_holds=true;
  }
  else if(fname==function_name)
  {
    status() << "Havoc recursive function call to " << fname << eom;
    precondition_holds=true;
  }
  else
  {
    status() << "Function " << fname << " not analyzed yet" << eom;
    return false; // function not seen yet
  }

  if(precondition_holds)
    return true;

  assert(!assertion.is_nil());

  // precondition check
  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  solver << precondition;
  solver << ssa_inliner.get_summaries(SSA);

  // add precondition
  solver << not_exprt(assertion);

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
  {
    precondition_holds=false;

    status() << "Precondition does not hold, need to recompute summary." << eom;
    break;
  }
  case decision_proceduret::D_UNSATISFIABLE:
  {
    precondition_holds=true;

    status() << "Precondition holds, replacing by summary." << eom;
    summaries_used++;

    break;
  }
  default: assert(false); break;
  }

  solver.pop_context();

  return precondition_holds;
}

/*******************************************************************\

Function: summarizer_baset::check_end_reachable

  Inputs:

 Outputs:

 Purpose: returns false if the end of the function is not reachable

\*******************************************************************/

bool summarizer_baset::check_end_reachable(
  const function_namet &function_name,
  local_SSAt &SSA,
  const exprt &cond)
{
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << ssa_inliner.get_summaries(SSA);

  solver << cond;

  exprt::operandst assertions;
  // do not add assertions
  //  because a failing assertion does not prove termination
  assertions.push_back(
    not_exprt(SSA.guard_symbol(--SSA.goto_function.body.instructions.end())));

  solver << not_exprt(conjunction(assertions)); // we want to reach any of them

  bool result=(solver()==decision_proceduret::D_SATISFIABLE);

  solver.pop_context();

  return result;
}

/*******************************************************************\

Function: summarizer_baset::get_loophead_selects

  Inputs:

 Outputs:

 Purpose: returns the select guards at the loop heads 
          e.g. in order to check whether a countermodel is spurious

\*******************************************************************/

void summarizer_baset::get_loophead_selects(
    const local_SSAt &SSA,
    const ssa_local_unwindert &ssa_local_unwinder,
    prop_convt &solver,
    exprt::operandst &loophead_selects)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead==SSA.nodes.end()) continue;
    symbol_exprt lsguard = SSA.name(SSA.guard_symbol(),
				    local_SSAt::LOOP_SELECT, n_it->location);
    ssa_local_unwinder.unwinder_rename(lsguard,*n_it,true);
    loophead_selects.push_back(not_exprt(lsguard));
    solver.set_frozen(solver.convert(lsguard));
  }
  literalt loophead_selects_literal = solver.convert(conjunction(loophead_selects));
  if(!loophead_selects_literal.is_constant())
    solver.set_frozen(loophead_selects_literal);

#if 0
  std::cout << "loophead_selects: "
	    << from_expr(SSA.ns,"",conjunction(loophead_selects))
	    << std::endl;
#endif
}

/*******************************************************************\

Function: summarizer_baset::get_loop_continues

  Inputs:

 Outputs:

 Purpose: returns the loop continuation guards at the end of the
          loops in order to check whether we can unroll further

\*******************************************************************/

void summarizer_baset::get_loop_continues(
  const local_SSAt &SSA,   
  ssa_local_unwindert &ssa_local_unwinder,
  exprt::operandst &loop_continues)
{
  //TODO: this should be provided by unwindable_local_SSA

  ssa_local_unwinder.compute_loop_continuation_conditions();
  ssa_local_unwinder.loop_continuation_conditions(loop_continues);
  if(loop_continues.size()==0) 
  {
    //TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
	n_it != SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end()) continue;
      symbol_exprt guard = SSA.guard_symbol(n_it->location);
      symbol_exprt cond = SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard,cond));
    }
  }

#if 0
  std::cout << "loophead_continues: " << from_expr(SSA.ns,"",disjunction(loop_continues)) << std::endl;
#endif
}

void summarizer_baset::get_loop_continues(
  const local_SSAt &SSA,   
  const ssa_local_unwindert &ssa_local_unwinder,
  const local_SSAt::locationt &loop_id,
  exprt::operandst &loop_continues)
{
  //TODO: need to ask ssa_inliner regarding inlined functions

  //TODO: this should be provided by unwindable_local_SSA

  //ssa_local_unwinder.loop_continuation_conditions(loop_id, loop_continues);
  ssa_local_unwinder.loop_continuation_conditions(loop_continues);
  if(loop_continues.size()==0) 
  {
    //TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
	n_it != SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end()) continue;
      if(n_it->loophead->location!=loop_id) continue;
      symbol_exprt guard = SSA.guard_symbol(n_it->location);
      symbol_exprt cond = SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard,cond));
      break;
    }
  }

#if 0
  std::cout << "loophead_continues: " << from_expr(SSA.ns,"",disjunction(loop_continues)) << std::endl;
#endif
}


/*******************************************************************\

Function: summarizer_baset::is_fully_unwound

  Inputs:

 Outputs:

 Purpose: checks whether the loops have been fully unwound

\*******************************************************************/

bool summarizer_baset::is_fully_unwound(
  const exprt::operandst &loop_continues, 
  const exprt::operandst &loophead_selects,
  incremental_solvert &solver)
{
  solver.new_context();
  solver << and_exprt(conjunction(loophead_selects),
		      disjunction(loop_continues));

  solver_calls++; //statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    solver.pop_context();
    return false;
    break;
      
  case decision_proceduret::D_UNSATISFIABLE:
    solver.pop_context();
    solver << conjunction(loophead_selects); 
    return true;
    break;

  case decision_proceduret::D_ERROR:    
  default:
    throw "error from decision procedure";
  }
}

