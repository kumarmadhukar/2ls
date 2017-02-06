/*******************************************************************\

Module: Summarizer for Backward Analysis

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_bw_cex_ai.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../domains/disjunctive_analyzer.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizer_bw_cex_ait::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_ait::summarize(const function_namet &function_name)
{
  exprt postcondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  compute_summary_rec(function_name,summaryt::entry_call_site,
		      postcondition,true);
}

/*******************************************************************\

Function: summarizer_bw_cex_ait::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_ait::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis (abstract)..." << eom;
  error_assertion = _error_assertion;

  summarize(entry_function);
}

/*******************************************************************\

Function: summarizer_bw_cex_ait::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_ait::check()
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

  //we are only complete if we are in the entry function
  if(result == property_checkert::UNKNOWN &&
     entry_function == error_function)
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

Function: summarizer_bw_cex_ait::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*******************************************************************\

Function: summarizer_bw_cex_ait::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_ait::compute_summary_rec(
  const function_namet &function_name,
  const summaryt::call_sitet &call_site,
  const exprt &_postcondition,
  bool context_sensitive)
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
  debug() << "Postcondition: " << 
    from_expr(SSA.ns, "", postcondition) << eom;
#endif

  if(_postcondition.is_false()){
    
    summary.error_summaries[call_site] = false_exprt();
    
  }
  else{ 

    // recursively compute summaries for function calls
    inline_summaries(function_name,SSA,summary,
		     postcondition,context_sensitive,
		     true); 
    
    status() << "Analyzing function "  << function_name << eom;
    
    do_summary(function_name,call_site,SSA,summary,summary,postcondition,context_sensitive);
    
    if(function_name == error_function)
      summary.has_assertion = true;
    
  }

  summary_db.set(function_name,summary);

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out,SSA.ns);   
    debug() << out.str() << eom;
  }

}

/*******************************************************************\

Function: summarizer_bw_cex_ait::do_summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_ait::do_summary(const function_namet &function_name, 
				       const summaryt::call_sitet &call_site,
				       local_SSAt &SSA,
				       const summaryt &old_summary,
				       summaryt &summary,
				       const exprt &postcondition,
				       bool context_sensitive)
{
  status() << "Computing error summary" << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  //TODO: maybe allow setting this separately on the command line
  optionst _options = options;
  _options.set_option("intervals",true);
  _options.set_option("binsearch-solver",true);
  
  //TODO: use a template generator without invariants
  template_generator_summaryt template_generator(
    _options,ssa_db,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,false);

  exprt::operandst c;
  //add forward information if available
  if(!old_summary.fw_precondition.is_nil())
    c.push_back(old_summary.fw_precondition);
  if(!old_summary.fw_invariant.is_nil())
    c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries
  exprt::operandst assert_postcond, noassert_postcond;
  // add error summaries for function calls
  bool assertion_flag;
  assertion_flag = ssa_inliner.get_summaries(SSA,call_site,false,
	      assert_postcond,noassert_postcond,c); //backward summaries

  assert_postcond.push_back(postcondition);  //context

  //add nondet variables from callees to summary.nondets
  std::set<exprt> summary_vars;
  find_symbols(conjunction(assert_postcond),summary_vars);
  for(std::set<exprt>::const_iterator it = summary_vars.begin();
      it != summary_vars.end(); ++it)
    if(it->id()==ID_nondet_symbol)
      summary.nondets.insert(*it);

  // assumptions must hold
  for(local_SSAt::nodest::const_iterator 
	n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end();
      ++n_it)
    for(local_SSAt::nodet::assumptionst::const_iterator 
	  a_it = n_it->assumptions.begin(); 
	a_it != n_it->assumptions.end();
	++a_it)
      c.push_back(*a_it);




#if 0
  std::cout << from_expr(SSA.ns, "", cc) << std::endl;
#endif

  //TODO: pushing loophead_selects into the solver

  summary.error_summaries[call_site];
  if(!template_generator.empty())
  {
    c.push_back(conjunction(assert_postcond)); //with negative information would need: not_exprt
    c.push_back(conjunction(noassert_postcond)); //with negative information would need: not_exprt dis

    //std::cout << "unsimplified constraints (if): " << from_expr(SSA.ns, "", conjunction(c)) << "\n\n\n";
    exprt cc = simplify_expr(conjunction(c), SSA.ns);
    //exprt cc = conjunction(c);
    //std::cout << "simplified constraints passed (if): " << from_expr(SSA.ns, "", cc) << "\n\n\n";

    /*
    ssa_analyzert analyzer;
    analyzer.set_message_handler(get_message_handler());
    analyzer(solver,SSA,cc,template_generator);
    analyzer.get_result(summary.error_summaries[call_site],
			template_generator.inout_vars());
    */
    /**/
    disjunctive_analyzert disjunctive_analyzer;
    disjunctive_analyzer.set_message_handler(get_message_handler());
    disjunctive_analyzer(solver,SSA,cc,template_generator,
			 cc,summary.error_summaries[call_site],
			 template_generator.inout_vars());
    /**/

#if 0
    std::cout << "SUM: " << from_expr(SSA.ns, "", summary.error_summaries[call_site]) << std::endl;
#endif


    summary.error_summaries[call_site] = 
      simplify_expr(summary.error_summaries[call_site], SSA.ns);


#if 0
    std::cout << "SUM (post simplification): " << from_expr(SSA.ns, "", summary.error_summaries[call_site]) << std::endl;
#endif

    //statistics
    /*
    solver_instances += analyzer.get_number_of_solver_instances();
    solver_calls += analyzer.get_number_of_solver_calls();
    */
    solver_instances += disjunctive_analyzer.get_number_of_solver_instances();
    solver_calls += disjunctive_analyzer.get_number_of_solver_calls();
    
  }
  else // TODO: yet another workaround for ssa_analyzer not being able to handle empty templates properly
  {
    c.push_back(conjunction(assert_postcond)); //with negative information would need: not_exprt
    c.push_back(conjunction(noassert_postcond)); //with negative information would need: not_exprt dis
    //c.push_back(not_exprt(conjunction(assert_postcond)));
    //c.push_back(not_exprt(disjunction(noassert_postcond)));

    //std::cout << "unsimplified constraints (else): " << from_expr(SSA.ns, "", conjunction(c)) << "\n\n\n";
    exprt cc = simplify_expr(conjunction(c), SSA.ns);
    //exprt cc = conjunction(c);
    //std::cout << "simplified constraints passed (else): " << from_expr(SSA.ns, "", cc) << "\n\n\n";

    //std::cout << "enabling expressions (else): " << from_expr(SSA.ns, "", SSA.get_enabling_exprs()) << "\n\n\n";

    solver << SSA;
    solver.new_context();
    solver << SSA.get_enabling_exprs();
    solver << cc;
    exprt result = true_exprt();
    if(solver()!=decision_proceduret::D_SATISFIABLE) result = false_exprt();
    solver.pop_context();
    summary.error_summaries[call_site] = result;

#if 0
    std::cout << "SUM: " << from_expr(SSA.ns, "", summary.error_summaries[call_site]) << std::endl;
#endif
  }

  summary.error_summaries[call_site] = 
    simplify_expr((summary.error_summaries[call_site]), SSA.ns); //not_exprt
  
  summary.has_assertion = assertion_flag;
}

/*******************************************************************\

Function: summarizer_bw_cex_ait::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_ait::inline_summaries(const function_namet &function_name, 
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

      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      status() << "Recursively summarizing function " << fname << eom;
      compute_summary_rec(fname,summaryt::call_sitet(n_it->location),
			  postcondition_call,context_sensitive);
    }
  }
}

/*******************************************************************\

Function: summarizer_bw_cex_ait::compute_calling_context2()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt summarizer_bw_cex_ait::compute_calling_context2(  
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
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  //analyze
  /*
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());
  */
  
  disjunctive_analyzert disjunctive_analyzer;
  disjunctive_analyzer.set_message_handler(get_message_handler());

  //TODO: maybe allow setting this separately on the command line
  optionst _options = options;
  _options.set_option("intervals",true);
  _options.set_option("binsearch-solver",true);

  //TODO: use a template generator without invariants
  template_generator_callingcontextt template_generator(
    _options,ssa_db,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,n_it,f_it,false);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::const_iterator, local_SSAt::var_sett>
    cs_globals_out;
  SSA.get_globals(n_it->location,cs_globals_out[f_it],false);

  exprt::operandst c;

  //add forward information if available
  if(!old_summary.fw_precondition.is_nil())
    c.push_back(old_summary.fw_precondition);
  if(!old_summary.fw_invariant.is_nil())
    c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries

  exprt::operandst assert_postcond, noassert_postcond;
  // add error summaries for function calls
  ssa_inliner.get_summaries(SSA,summaryt::call_sitet(n_it->location),false,
			    assert_postcond,noassert_postcond,c); //backward summaries
  assert_postcond.push_back(postcondition);  //context

  
  //TODO: pushing loophead_selects into the solver

  // set preconditions
  local_SSAt &fSSA = ssa_db.get(fname); 

  exprt postcondition_call;

  if(!template_generator.empty()){

    c.push_back(conjunction(assert_postcond)); //with negative information would need: not_exprt
    c.push_back(conjunction(noassert_postcond)); //with negative information would need: not_exprt dis

    /*
    analyzer(solver,SSA,conjunction(c),template_generator);
    analyzer.get_result(postcondition_call,
			template_generator.callingcontext_vars());  
    */
  
    disjunctive_analyzer(solver,SSA,conjunction(c),template_generator,
			 conjunction(c), postcondition_call,
			 template_generator.callingcontext_vars());

    ssa_inliner.rename_to_callee(f_it, fSSA.params,
				 cs_globals_out[f_it],fSSA.globals_out,
				 postcondition_call);

  }
  else{ // TODO: yet another workaround for ssa_analyzer not being able to handle empty templates properly

    c.push_back(not_exprt(conjunction(assert_postcond)));
    c.push_back(not_exprt(disjunction(noassert_postcond)));

    solver << SSA;
    solver.new_context();
    solver << SSA.get_enabling_exprs();
    solver << conjunction(c);

    //std::cout << "passed to solver, else branch, calling context: " << from_expr(SSA.ns, "", conjunction(c)) << "\n\n";
    
    postcondition_call = false_exprt();
    if(solver()!=decision_proceduret::D_SATISFIABLE) postcondition_call = true_exprt();
    solver.pop_context();
  }

  debug() << "Backward calling context for " << 
    from_expr(SSA.ns, "", *f_it) << ": " 
	  << from_expr(SSA.ns, "", postcondition_call) << eom;

  //statistics
  /*
  solver_instances += analyzer.get_number_of_solver_instances();
  solver_calls += analyzer.get_number_of_solver_calls();
  */
  solver_instances += disjunctive_analyzer.get_number_of_solver_instances();
  solver_calls += disjunctive_analyzer.get_number_of_solver_calls();
  
  return postcondition_call;
}


