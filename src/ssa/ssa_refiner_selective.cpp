/*******************************************************************\

Module: SSA Refiner for selective unwinding and inlining

Author: Peter Schrammel, Madhukar Kumar

\*******************************************************************/

#include "ssa_refiner_selective.h"

/*******************************************************************\

Function: ssa_refiner_selectivet::operator()

  Inputs:

 Outputs:

 Purpose: refine selectively according to the given reason

\*******************************************************************/

bool ssa_refiner_selectivet::operator()()
{
  // unwind loops "selectively" (those that seem to be the "reason")
  for(reasont::const_iterator it = reason.begin(); it != reason.end(); ++it)
  {
    for(std::set<reason_infot::loop_infot>::const_iterator l_it = 
          it->second.loops.begin();
        l_it != it->second.loops.end(); l_it++)
    {
      unsigned new_unwind = ssa_unwinder.unwind_loop_once_more(it->first, 
                                             (*l_it)->location_number);
      debug() << "Refining function " << it->first << ": unwinding loop at " 
              << (*l_it)->location_number << " (k=" << new_unwind << ")" << eom;
      unwind = std::max(unwind, new_unwind);
    }
  }

  // inline functions "selectively" (those that seem to be the "reason")
  for(reasont::const_iterator it = reason.begin(); it != reason.end(); ++it)
  {
    for(std::set<reason_infot::function_infot>::const_iterator f_it = 
          it->second.functions.begin();
        f_it != it->second.functions.end(); f_it++)
    {
      local_SSAt &SSA = ssa_db.get(it->first);
      local_SSAt::nodest::iterator n_it = SSA.find_node(*f_it);
      assert(n_it->function_calls.size()==1);
      n_it->function_calls_inlined = true;

      irep_idt fname = to_symbol_expr(n_it->function_calls.begin()
                                      ->function()).get_identifier();
      debug() << "Refining function " << it->first << ": inlining call to " 
              << fname << " at " << (*f_it)->location_number<< eom;
    }
  }

  return unwind<=max_unwind;
}
