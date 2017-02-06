/*******************************************************************\

Module: SSA Refiner for Monolithic Analysis

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_REFINER_MONOLITHIC_H
#define CPROVER_SSA_REFINER_MONOLITHIC_H

#include "ssa_refiner.h"

#include "../summarizer/summary_db.h"
#include "ssa_unwinder.h"

class summary_dbt;
class ssa_unwindert;

class ssa_refiner_monolithict : public ssa_refinert
{
 public:
  explicit ssa_refiner_monolithict(
    summary_dbt &_summary_db,
    ssa_unwindert &_ssa_unwinder,
    unsigned _max_unwind
    ) : 
      summary_db(_summary_db),
      ssa_unwinder(_ssa_unwinder),
      max_unwind(_max_unwind),
      unwind(0)
    {}

    virtual bool operator()(); 
    virtual unsigned get_unwind() { return unwind>0 ? unwind-1 : 0; }
  
 protected:
  summary_dbt &summary_db;
  ssa_unwindert &ssa_unwinder;
  const unsigned max_unwind;
  unsigned unwind;
};

#endif
