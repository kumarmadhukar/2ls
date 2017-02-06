/*******************************************************************\

Module: SSA Refiner Base Class

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_REFINER_H
#define CPROVER_SSA_REFINER_H

#include <util/message.h>

class ssa_refinert : public messaget
{
 public:
  virtual bool operator()() { assert(false); }
  virtual unsigned get_unwind() { assert(false); }
};

#endif
