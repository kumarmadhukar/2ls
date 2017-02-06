/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_kind.h"
#include "../ssa/ssa_refiner.h"
#include "../ssa/ssa_refiner_monolithic.h"
#include "../ssa/ssa_refiner_selective.h"

#define GIVE_UP_INVARIANTS 7

/*******************************************************************\

Function: summary_checker_kindt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_kindt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
    entry_function = "";

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(true,false);

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
        //TODO: update only those that were refined by unwinding
        SSA_dependency_graphs(goto_model, ns);
      }
    }

    //check
    std::set<irep_idt> seen_function_calls;
    result =  check_properties(entry_function, entry_function, 
                               seen_function_calls, false); 

    //do static analysis and check again
    if(result == property_checkert::UNKNOWN &&
       !options.get_bool_option("havoc") && 
       (unwind<GIVE_UP_INVARIANTS || 
        !options.get_bool_option("competition-mode"))) //magic constant 
    {
      summarize(goto_model);
      std::set<irep_idt> seen_function_calls;
      result =  check_properties(entry_function, entry_function, 
                                 seen_function_calls, false); 
    }

    //result
    if(result == property_checkert::PASS) 
    {
      status() << "k-induction proof found after " 
               << unwind << " unwinding(s)" << eom;
      break;
    }
    else if(result == property_checkert::FAIL) 
    {
      status() << "k-induction counterexample found after " 
               << unwind << " unwinding(s)" << eom;
      break;
    }
  }
  delete ssa_refiner;
  report_statistics();
  return result;
}

