/*******************************************************************\

Module: Slicing-based WP Counterexample-based Backward Analysis

Author: Madhukar Kumar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BW_CEX_WP_H
#define CPROVER_SUMMARIZER_BW_CEX_WP_H

#include <util/message.h>
#include <goto-programs/property_checker.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include <util/time_stopping.h>

#include "summarizer_bw_cex.h"

class summarizer_bw_cex_wpt : public summarizer_bw_cex_baset
{
 public:
  explicit summarizer_bw_cex_wpt(optionst &_options,
				       summary_dbt &_summary_db,
				       ssa_dbt &_ssa_db,
				       ssa_unwindert &_ssa_unwinder,
				       ssa_inlinert &_ssa_inliner,
				       incremental_solvert &_solver,
				       function_namet _entry_function,
				       function_namet _error_function):
    summarizer_bw_cex_baset(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner,
			  _entry_function,_error_function),
    solver(_solver)
    {}
  
  virtual void summarize(const function_namet &entry_function);
  virtual void summarize(const exprt &_error_assertion);

  virtual property_checkert::resultt check();
  
 protected:
  incremental_solvert &solver;

  virtual find_symbols_sett inline_summaries(
				     const function_namet &function_name,
				     const find_symbols_sett &dependency_set,
				     int counter,
                                     exprt &error_summary);
  
  virtual find_symbols_sett compute_summary_rec(
					const function_namet &function_name,
					const find_symbols_sett &dependency_set,
					int counter,
					const summaryt::call_sitet &call_site);
  virtual void debug_print(
			const function_namet &function_name,
			find_symbols_sett &dependency_set);

  exprt simplify_summary(const namespacet &ns, 
			 exprt summary,
			 const find_symbols_sett &vars);
  void simplify_summary_build_map(
    replace_mapt &replace_map, const exprt &expr);
  bool simplify_summary_replace(
    const replace_mapt &replace_map, exprt &expr);
  void simplify_summary_cleanup(
    const find_symbols_sett &vars, exprt &expr);

};


#endif
