/*******************************************************************\

Module: SSA Refiner for Monolithic Analysis

Author: Peter Schrammel

\*******************************************************************/

#include "ssa_refiner_monolithic.h"

/*******************************************************************\

Function: ssa_refiner_monolithict::operator()

  Inputs:

 Outputs:

 Purpose: refine all

\*******************************************************************/

bool ssa_refiner_monolithict::operator()()
{
  status() << "Unwinding (k=" << unwind << ")" << eom;
  summary_db.mark_recompute_all(); //TODO: recompute only functions with loops
  ssa_unwinder.unwind_all(unwind);

  return unwind++<=max_unwind;
}
