/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

#include <util/prefix.h>

#include "summary_checker_ai.h"

/*******************************************************************\

Function: summary_checker_ait::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_ait::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(false,false);

  unsigned unwind = options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;

    ssa_unwinder.init_localunwinders();

    ssa_unwinder.unwind_all(unwind);
  }

#if 0
  /*********************************************************************************/
  /**************** code to test the loop-specific unwind function *****************/
  /**/
  if(unwind > 0){
    forall_goto_functions(f_it, goto_model.goto_functions){
      if(!f_it->second.body_available()) continue;
      if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
      local_SSAt &SSA = ssa_db.get(f_it->first);
      std::cout << "==>> Output SSA for function: " << f_it->first << "\n";
      SSA.output(std::cout);
    }
  }
  else{
    ssa_unwinder.init_localunwinders(); // possibly required;
    
    // iterate over the SSA to unwind loops
    forall_goto_functions(f_it, goto_model.goto_functions){
      
      if(!f_it->second.body_available()) continue;
      if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
      
      local_SSAt &SSA = ssa_db.get(f_it->first);
      for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
          n_it != SSA.nodes.end(); n_it++){
        if(n_it->loophead!=SSA.nodes.end()){
          std::cout << "==>> unwinding loop with location number: "
                    << n_it->loophead->location->location_number << "\n";
          ssa_unwinder.unwind_loop_alone(f_it->first,
                                         n_it->loophead->location->location_number, 1);
        }
      }
    }
    
    forall_goto_functions(f_it, goto_model.goto_functions){
      if(!f_it->second.body_available()) continue;
      if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
      local_SSAt &SSA = ssa_db.get(f_it->first);
      std::cout << "==>> Output SSA for function: " << f_it->first << "\n";
      SSA.output(std::cout);
    }
    
  }
  /**/
  /*********************************************************************************/
#endif

  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";

  if(!(options.get_bool_option("inline")))
  {
    if((options.get_option("spurious-check") != "concrete") &&
       (options.get_option("spurious-check") != "abstract"))
    {
      SSA_dependency_graphs(goto_model, ns);
    }
  }

  // properties
  initialize_property_map(goto_model.goto_functions);

  bool preconditions = options.get_bool_option("preconditions");
  bool termination = options.get_bool_option("termination");
  bool trivial_domain = options.get_bool_option("havoc");
  if(!trivial_domain || termination)
  {
    //forward analysis
    summarize(goto_model,true,termination);
  }
  if(!trivial_domain && preconditions)
  {
    //backward analysis
    summarize(goto_model,false,termination);
  }

  if(preconditions) 
  {
    report_statistics();
    report_preconditions();
    return property_checkert::UNKNOWN;
  }

  if(termination) 
  {
    report_statistics();
    return report_termination();
  }

#ifdef SHOW_CALLINGCONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    return property_checkert::UNKNOWN;
#endif

/*
  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";
*/

  std::set<irep_idt> seen_function_calls;
  property_checkert::resultt result =  check_properties(entry_function, entry_function, seen_function_calls, false); 
  report_statistics();
  return result;
}


/*******************************************************************\

Function: summary_checker_ait::report_preconditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_ait::report_preconditions()
{
  result() << eom;
  result() << "** " << (options.get_bool_option("sufficient") ? 
			"Sufficient" : "Necessary")
	   << " preconditions: " << eom;
  ssa_dbt::functionst &functions = ssa_db.functions();
  for(ssa_dbt::functionst::iterator it = functions.begin();
      it != functions.end(); it++)
  {
    exprt precondition;
    bool computed = summary_db.exists(it->first);
    if(computed) precondition = summary_db.get(it->first).bw_precondition;
    if(precondition.is_nil()) computed = false;
    result() << eom << "[" << it->first << "]: " 
	     << (!computed ? "not computed" : 
		 from_expr(it->second->ns, "", precondition)) << eom;
  }
}

/*******************************************************************\

Function: summary_checker_ait::report_termination

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_ait::report_termination()
{
  result() << eom;
  result() << "** Termination: " << eom;
  bool not_computed = true; 
  bool all_terminate = true; 
  bool one_nonterminate = false; 
  ssa_dbt::functionst &functions = ssa_db.functions();
  for(ssa_dbt::functionst::iterator it = functions.begin();
      it != functions.end(); it++)
  {
    threevalt terminates = YES;
    bool computed = summary_db.exists(it->first);
    if(computed) 
    {
      terminates = summary_db.get(it->first).terminates;
      not_computed = false;
    }
    all_terminate = all_terminate && (terminates==YES);
    one_nonterminate = one_nonterminate || (terminates==NO);
    result() << "[" << it->first << "]: " 
	     << (!computed ? "not computed" : threeval2string(terminates)) << eom;
  }
  if(not_computed) return property_checkert::UNKNOWN;
  if(all_terminate) return property_checkert::PASS;
  if(one_nonterminate) return property_checkert::FAIL;
  return property_checkert::UNKNOWN;
}
