/*******************************************************************\

Module: Counterexample-based Backward Analysis All

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BW_CEX_ALL_H
#define CPROVER_SUMMARIZER_BW_CEX_ALL_H

#include <util/message.h>
#include <goto-programs/property_checker.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include "summarizer_bw_cex.h"
#include "summarizer_bw_cex_concrete.h"
#include "summarizer_bw_cex_ai.h"
#include "summarizer_bw_cex_complete.h"

class summarizer_bw_cex_allt : public summarizer_bw_cex_baset
{
 public:
   explicit summarizer_bw_cex_allt(optionst &_options,
				   summary_dbt &_summary_db,
				   ssa_dbt &_ssa_db,
				   ssa_unwindert &_ssa_unwinder,
				   ssa_inlinert &_ssa_inliner,
				   incremental_solvert &_solver,
				   function_namet _entry_function,
				   function_namet _error_function):
      summarizer_bw_cex_baset(_options,_summary_db,_ssa_db,
			      _ssa_unwinder,_ssa_inliner,
			      _entry_function,_error_function),
      summarizer_bw_cex_concrete(_options,_summary_db,_ssa_db,
				 _ssa_unwinder,_ssa_inliner,
				 _entry_function,_error_function),
      summarizer_bw_cex_ai(_options,_summary_db,_ssa_db,
			   _ssa_unwinder,_ssa_inliner,
			   _entry_function,_error_function),
      summarizer_bw_cex_complete(_options,_summary_db,_ssa_db,
				 _ssa_unwinder,_ssa_inliner,
				 _solver,_entry_function,_error_function),
      result(property_checkert::UNKNOWN)
    {}

  virtual void summarize(const exprt &_error_assertion);

  virtual void set_message_handler(message_handlert &handler)
  {
    summarizer_bw_cex_concrete.set_message_handler(handler);
    summarizer_bw_cex_ai.set_message_handler(handler);
    summarizer_bw_cex_complete.set_message_handler(handler);
    messaget::set_message_handler(handler);
  }


  virtual property_checkert::resultt check();
  
 protected:
  summarizer_bw_cex_concretet summarizer_bw_cex_concrete;
  summarizer_bw_cex_ait summarizer_bw_cex_ai;
  summarizer_bw_cex_completet summarizer_bw_cex_complete;
  property_checkert::resultt result;

};


#endif
