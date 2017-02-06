/*******************************************************************\

Module: Summarizer Base

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BASE_H
#define CPROVER_SUMMARIZER_BASE_H

#include <util/message.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include <util/time_stopping.h>

class summarizer_baset : public messaget
{
 public:
 explicit summarizer_baset(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner) : 
    options(_options),
    summary_db(_summary_db),
    ssa_db(_ssa_db),
    ssa_unwinder(_ssa_unwinder),
    ssa_inliner(_ssa_inliner),
    nonpassed_assertions(false),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0),
    termargs_computed(0)
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef ssa_dbt::functionst functionst;
  typedef functionst::value_type functiont;

  virtual void summarize(); 
  virtual void summarize(const function_namet &entry_function); 

  static void get_loop_continues(
    const local_SSAt &SSA,   
    ssa_local_unwindert &ssa_local_unwinder,
    exprt::operandst &loop_continues);

  static void get_loop_continues(
    const local_SSAt &SSA,   
    const ssa_local_unwindert &ssa_local_unwinder,
    const local_SSAt::locationt &loop_id,
    exprt::operandst &loop_continues);

  static void get_loophead_selects(
    const local_SSAt &SSA,   
    const ssa_local_unwindert &ssa_local_unwinder,
    prop_convt &solver,
    exprt::operandst &loophead_selects);

  inline unsigned get_number_of_solver_instances() { return solver_instances; }
  inline unsigned get_number_of_solver_calls() { return solver_calls; }
  inline unsigned get_number_of_summaries_used() { return summaries_used; }
  inline unsigned get_number_of_termargs_computed() { return termargs_computed; }

 protected:
  optionst &options;
  summary_dbt &summary_db;
  ssa_dbt &ssa_db;
  ssa_unwindert &ssa_unwinder;
  ssa_inlinert &ssa_inliner;
  bool nonpassed_assertions;

  virtual void compute_summary_rec(const function_namet &function_name,
				   const exprt &precondition,
				   bool context_sensitive) 
    { assert(false); }

  bool check_call_reachable(const function_namet &function_name,
			    local_SSAt &SSA,
			    local_SSAt::nodest::const_iterator n_it, 
			    local_SSAt::nodet::function_callst::const_iterator f_it,
			    const exprt& precondition,
			    bool forward);

  virtual exprt compute_calling_context(
			const function_namet &function_name, 
			local_SSAt &SSA,
			local_SSAt::nodest::const_iterator n_it, 
			local_SSAt::nodet::function_callst::const_iterator f_it,
			const exprt &precondition,
			bool forward);

  virtual bool check_precondition(const function_namet &function_name, 
                          local_SSAt &SSA,
			  local_SSAt::nodest::const_iterator node, 
			  local_SSAt::nodet::function_callst::const_iterator f_it,
    		          const exprt &precondition,
                          bool context_sensitive);

  void get_assertions(const local_SSAt &SSA,
		      exprt::operandst &assertions);

  bool check_end_reachable(const function_namet &function_name,
			   local_SSAt &SSA, 
			   const exprt &cond);

  bool is_fully_unwound(
    const exprt::operandst &loop_continues, 
    const exprt::operandst &loophead_selects,
    incremental_solvert &solver);

  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
  unsigned termargs_computed;
};


#endif
