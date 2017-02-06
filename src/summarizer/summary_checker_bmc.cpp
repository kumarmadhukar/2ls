/*******************************************************************\

Module: Summarizer Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_bmc.h"

#include "../ssa/ssa_refiner.h"
#include "../ssa/ssa_refiner_monolithic.h"
#include "../ssa/ssa_refiner_selective.h"


/*******************************************************************\

Function: summary_checker_bmct::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_bmct::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(false,true);

  property_checkert::resultt result = property_checkert::UNKNOWN;
  unsigned max_unwind = options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  ssa_refinert *ssa_refiner;
  if((options.get_bool_option("inline")))
    ssa_refiner = new ssa_refiner_monolithict(summary_db, ssa_unwinder, 
                                              max_unwind);
  else
    ssa_refiner = new ssa_refiner_selectivet(ssa_db, ssa_unwinder, 
                                             max_unwind, ssa_inliner, reason);
  ssa_refiner->set_message_handler(get_message_handler());

  //while can refine
  while((*ssa_refiner)())
  {
    unsigned unwind = ssa_refiner->get_unwind();

    //dependency graphs
    if(!(options.get_bool_option("inline")))
    {
      if((options.get_option("spurious-check") != "concrete") &&
         (options.get_option("spurious-check") != "abstract"))
      {
        SSA_dependency_graphs(goto_model, ns);
      }
    }

    //check
    std::set<irep_idt> seen_function_calls;
    result =  check_properties(entry_function, entry_function, 
                               seen_function_calls, false); 

    //result
    if(result == property_checkert::PASS) 
    {
      status() << "incremental BMC proof found after " 
	       << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result == property_checkert::FAIL) 
    {
      status() << "incremental BMC counterexample found after " 
	       << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}
