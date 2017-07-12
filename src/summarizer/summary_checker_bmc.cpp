/*******************************************************************\

Module: Summarizer Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_bmc.h"


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

  for(unsigned unwind = 0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    summary_db.mark_recompute_all();
    ssa_unwinder.unwind_all(unwind+1);
    std::set<irep_idt> seen_function_calls;
    result =  check_properties(entry_function, entry_function, seen_function_calls); 
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
