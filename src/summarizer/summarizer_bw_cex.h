/*******************************************************************\

Module: Counterexample-based Backward Analysis Base

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BW_CEX_H
#define CPROVER_SUMMARIZER_BW_CEX_H

#include <util/message.h>
#include <goto-programs/property_checker.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include "summarizer_bw.h"

class summarizer_bw_cex_baset : public summarizer_bwt
{
 public:
  virtual void summarize();
  virtual void summarize(const function_namet &entry_function);
  virtual void summarize(const exprt &_error_assertion);

  virtual property_checkert::resultt check();
  
 protected:
  function_namet entry_function;
  function_namet error_function;
  exprt error_assertion;

  explicit summarizer_bw_cex_baset(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner,
	     function_namet _entry_function,
	     function_namet _error_function): 
  summarizer_bwt(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner),
  entry_function(_entry_function),
  error_function(_error_function)
  {}

};


#endif
