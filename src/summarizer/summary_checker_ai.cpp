/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

#include <util/prefix.h>

#include "summary_checker_ai.h"

/*******************************************************************\

Function: summary_checker_ait::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_ait::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(false,false);

  unsigned unwind = options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;

    ssa_unwinder.init_localunwinders();

    ssa_unwinder.unwind_all(unwind+1);
    ssa_unwinder.output(debug()); debug() <<eom;
  }

  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";

  if(!(options.get_bool_option("inline"))){
    if((options.get_option("spurious-check") != "concrete") &&
       (options.get_option("spurious-check") != "abstract")){
      // compute dependency graph for all the functions
      forall_goto_functions(f_it, goto_model.goto_functions)
	{
	  if(!f_it->second.body_available()) continue;
	  if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
	  
	  status() << "Computing dependency graph of " << f_it->first << messaget::eom;
	  
	  //ssa_db.depgraph_create(f_it->first, ns, ssa_inliner);
	  
	  if(entry_function == f_it->first)
	    ssa_db.depgraph_create(f_it->first, ns, ssa_inliner, true);
	  else
	    ssa_db.depgraph_create(f_it->first, ns, ssa_inliner, false); // change to true if all functions are to be treated equal
	  
	  ssa_dependency_grapht &ssa_depgraph = ssa_db.get_depgraph(f_it->first);
	  ssa_depgraph.output(debug()); debug() << eom;
	  std::cout << "output SSA for function: " << f_it->first << "\n";
	  ssa_db.get(f_it->first).output_verbose(std::cout);
	}
    }
  }

  // properties
  initialize_property_map(goto_model.goto_functions);

  bool preconditions = options.get_bool_option("preconditions");
  if(!options.get_bool_option("havoc")) 
  {
    //forward analysis
    summarize(goto_model,true,false);
  }
  if(!options.get_bool_option("havoc") && preconditions)
  {
    //backward analysis
    summarize(goto_model,false,false);
  }

  if(preconditions) 
  {
    report_statistics();
    report_preconditions();
    return property_checkert::UNKNOWN;
  }

#ifdef SHOW_CALLINGCONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    return property_checkert::UNKNOWN;
#endif

/*
  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";
*/

  std::set<irep_idt> seen_function_calls;
  property_checkert::resultt result =  check_properties(entry_function, entry_function, seen_function_calls); 
  report_statistics();
  return result;
}


/*******************************************************************\

Function: summary_checker_ait::report_preconditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_ait::report_preconditions()
{
  result() << eom;
  result() << "** " << (options.get_bool_option("sufficient") ? 
			"Sufficient" : "Necessary")
	   << " preconditions: " << eom;
  ssa_dbt::functionst &functions = ssa_db.functions();
  for(ssa_dbt::functionst::iterator it = functions.begin();
      it != functions.end(); it++)
  {
    exprt precondition;
    bool computed = summary_db.exists(it->first);
    if(computed) precondition = summary_db.get(it->first).bw_precondition;
    if(precondition.is_nil()) computed = false;
    result() << eom << "[" << it->first << "]: " 
	     << (!computed ? "not computed" : 
		 from_expr(it->second->ns, "", precondition)) << eom;
  }
}
