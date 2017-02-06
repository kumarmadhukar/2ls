/*******************************************************************\

Module: SSA Refiner for selective unwinding and inlining

Author: Peter Schrammel, Madhukar Kumar

\*******************************************************************/

#ifndef CPROVER_SSA_REFINER_SELECTIVE_H
#define CPROVER_SSA_REFINER_SELECTIVE_H

#include "ssa_refiner.h"

#include "../summarizer/ssa_db.h"
#include "ssa_inliner.h"
#include "ssa_unwinder.h"

class ssa_dbt;

class ssa_refiner_selectivet : public ssa_refinert
{
 public:
  struct reason_infot
  {
    typedef local_SSAt::locationt function_infot; //call_site; restriction: we assume that there is a single function call in an SSA node
    typedef local_SSAt::locationt loop_infot;
    std::set<function_infot> functions;
    std::set<loop_infot> loops; 
  };

  class reasont : public std::map<irep_idt, reason_infot>
  {
  public:
    void merge(const reasont &other)
    {
      for(reasont::const_iterator it = other.begin();
          it != other.end(); ++it)
      {
        reason_infot &r = (*this)[it->first];
        r.functions.insert(it->second.functions.begin(), 
                           it->second.functions.end());
        r.loops.insert(it->second.loops.begin(), it->second.loops.end());
      }
    }
  };


  explicit ssa_refiner_selectivet(
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    unsigned _max_unwind,
    ssa_inlinert &_ssa_inliner,
    reasont &_reason
    ) : 
      ssa_db(_ssa_db),
      ssa_unwinder(_ssa_unwinder),
      max_unwind(_max_unwind),
      ssa_inliner(_ssa_inliner),
      unwind(0),
      reason(_reason)
    {}

    virtual bool operator()(); 
    virtual unsigned get_unwind() { return unwind; }
  
 protected:
  ssa_dbt &ssa_db;
  ssa_unwindert &ssa_unwinder;
  const unsigned max_unwind;
  ssa_inlinert &ssa_inliner;
  unsigned unwind;
  reasont &reason;
};

#endif
