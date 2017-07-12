/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_INLINER_H
#define CPROVER_SSA_INLINER_H

#include <util/message.h>

#include "../summarizer/summary_db.h"
#include "../summarizer/ssa_db.h"
#include "../ssa/local_ssa.h"

class summary_dbt;
class ssa_dbt;

class ssa_inlinert : public messaget
{
 public:
  explicit ssa_inlinert(summary_dbt &_summary_db) : 
  counter(0),
    summary_db(_summary_db)
    {}

  void get_guard_binding(const local_SSAt &SSA,
			 const local_SSAt &fSSA,
			 local_SSAt::nodest::const_iterator n_it,
			 exprt &guard_binding,
			 int counter);
  void get_bindings(const local_SSAt &SSA,
		    const local_SSAt &fSSA,
		    local_SSAt::nodest::const_iterator n_it,
		    local_SSAt::nodet::function_callst::const_iterator f_it, 
		    exprt::operandst &bindings_in,
		    exprt::operandst &bindings_out,
		    int counter);
  void get_summary(const local_SSAt &SSA,
		   local_SSAt::nodest::const_iterator n_it,
		   local_SSAt::nodet::function_callst::const_iterator f_it, 
		   const summaryt &summary,
		   bool forward, 
		   exprt::operandst &summaries,
		   exprt::operandst &bindings,
		   int counter,
		   bool error_summ = false);
  void get_summaries(const local_SSAt &SSA,
		     bool forward,
		     exprt::operandst &summaries,
		     exprt::operandst &bindings); //TODO: need to explicitly pass the correct counter
  bool get_summaries(const local_SSAt &SSA,
                     const summaryt::call_sitet &current_call_site,
		     bool forward,
		     exprt::operandst &assert_summaries,
		     exprt::operandst &noassert_summaries,
		     exprt::operandst &bindings); //TODO: need to explicitly pass the correct counter

  exprt get_summaries(const local_SSAt &SSA); //TODO: need to explicitly pass the correct counter
  
  void replace(local_SSAt &SSA,
	       local_SSAt::nodest::iterator node,
               local_SSAt::nodet::function_callst::iterator f_it, 
	       const local_SSAt::var_sett &cs_globals_in, 
	       //incoming globals at call site
	       const local_SSAt::var_sett &cs_globals_out, 
	       //outgoing globals at call site
               const summaryt &summary,
	       bool forward,
	       bool preconditions_as_assertions,
	       int counter);

  void replace(local_SSAt &SSA,
	       bool forward,
	       bool preconditions_as_assertions,
	       int counter);

  void replace(local_SSAt::nodest &nodes,
	       local_SSAt::nodest::iterator node, 
               local_SSAt::nodet::function_callst::iterator f_it, 
	       const local_SSAt::var_sett &cs_globals_in, 
	       //incoming globals at call site
	       const local_SSAt::var_sett &cs_globals_out, 
	       //outgoing globals at call site
               const local_SSAt &function,
	       int counter);

  void replace(local_SSAt &SSA,
               const ssa_dbt &ssa_db,
	       int counter,
               bool recursive=false,
               bool rename=true);
  
  void havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::function_callst::iterator f_it);

  //apply changes to node, must be called after replace and havoc
  void commit_node(local_SSAt::nodest::iterator node);
  bool commit_nodes(local_SSAt::nodest &nodes,
                    local_SSAt::nodest::iterator n_pos);

  //functions for renaming preconditions to calling context
  void rename_to_caller(local_SSAt::nodet::function_callst::const_iterator f_it, 
			const local_SSAt::var_listt &params, 
			const local_SSAt::var_sett &cs_globals_in, 
			const local_SSAt::var_sett &globals_in, 
			exprt &expr);
  void rename_to_callee(local_SSAt::nodet::function_callst::const_iterator f_it, 
			const local_SSAt::var_listt &params, 
			const local_SSAt::var_sett &cs_globals_in, 
			const local_SSAt::var_sett &globals_in, 
			exprt &expr);
  
  static bool find_corresponding_symbol(const symbol_exprt &s, 
				 const local_SSAt::var_sett &globals,
                                 symbol_exprt &s_found);

  static irep_idt get_original_identifier(const symbol_exprt &s);
  
  irep_idt rename(irep_idt &id, int counter);

  irep_idt rename(irep_idt &id, int counter, bool attach);

  int get_rename_counter(){
    counter++;
    return counter;
  }

  // moved from protected to public, for use in summarizer_bw_cex_complete
  void rename(exprt &expr, int counter);
  
 protected:
  unsigned counter;
  summary_dbt &summary_db;

  local_SSAt::nodest new_nodes;
  local_SSAt::nodet::equalitiest new_equs;
  std::set<local_SSAt::nodet::function_callst::iterator> rm_function_calls;

  void replace_globals_in(const local_SSAt::var_sett &globals_in, 
                          const local_SSAt::var_sett &globals,
			  int counter);
  void replace_params(const local_SSAt::var_listt &params,
                      const function_application_exprt &funapp_expr,
		      int counter);
  void replace_globals_out(const local_SSAt::var_sett &globals_out, 
			   const local_SSAt::var_sett &cs_globals_in,  
			   const local_SSAt::var_sett &cs_globals_out,
			   int counter);

  void get_replace_globals_in(const local_SSAt::var_sett &globals_in, 
			      const function_application_exprt &funapp_expr,
			      const local_SSAt::var_sett &globals,
			      exprt::operandst &c,
			      int counter);
  void get_replace_params(const local_SSAt &SSA,
			  const local_SSAt::var_listt &params,
			  local_SSAt::nodest::const_iterator n_it,
			  const function_application_exprt &funapp_expr,
			  exprt::operandst &c,
			  int counter);
  void get_replace_globals_out(const local_SSAt::var_sett &globals_out, 
			       const function_application_exprt &funapp_expr,
			       const local_SSAt::var_sett &cs_globals_in,  
			       const local_SSAt::var_sett &cs_globals_out,
			       exprt::operandst &c,
			       int counter);

  void rename(local_SSAt::nodet &node, int counter);

};


#endif
