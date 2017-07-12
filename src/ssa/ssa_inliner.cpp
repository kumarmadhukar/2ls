/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#include <util/i2string.h>
#include <util/replace_expr.h>

#include "ssa_inliner.h"

/*******************************************************************\

Function: ssa_inlinert::get_guard_binding

  Inputs:

 Outputs: 

 Purpose: get guard binding for function call

\*******************************************************************/

void ssa_inlinert::get_guard_binding(
 const local_SSAt &SSA,
 const local_SSAt &fSSA,
 local_SSAt::nodest::const_iterator n_it,
 exprt &guard_binding,
 int counter)
{
  exprt callee_guard, caller_guard;
  callee_guard = fSSA.guard_symbol(fSSA.goto_function.body.instructions.begin());
  rename(callee_guard, counter);
  caller_guard = SSA.guard_symbol(n_it->location);

  guard_binding = equal_exprt(callee_guard, caller_guard);
}

/*******************************************************************\

Function: ssa_inlinert::get_bindings

  Inputs:

 Outputs: 

 Purpose: get bindings for function call

\*******************************************************************/

void ssa_inlinert::get_bindings(
 const local_SSAt &SSA,
 const local_SSAt &fSSA,
 local_SSAt::nodest::const_iterator n_it,
 local_SSAt::nodet::function_callst::const_iterator f_it, 
 exprt::operandst &bindings_in,
 exprt::operandst &bindings_out,
 int counter)
{
  //getting globals at call site
  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
  goto_programt::const_targett loc = n_it->location;
  
  SSA.get_globals(loc,cs_globals_in);
  SSA.get_globals(loc,cs_globals_out,false);
  
#if 0
  std::cout << "cs_globals_in: ";
  for(summaryt::var_sett::const_iterator it = cs_globals_in.begin();
      it != cs_globals_in.end(); it++)
    std::cout << from_expr(SSA.ns,"",*it) << " ";
  std::cout << std::endl;

  std::cout << "cs_globals_out: ";
  for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
      it != cs_globals_out.end(); it++)
    std::cout << from_expr(SSA.ns,"",*it) << " ";
  std::cout << std::endl;
#endif

  //equalities for arguments
  //bindings_in.push_back(get_replace_params(SSA.params,*f_it));
  get_replace_params(SSA,fSSA.params,n_it,*f_it,bindings_in,counter);

  //equalities for globals_in
  //bindings_in.push_back(get_replace_globals_in(SSA.globals_in,cs_globals_in));

  //get_replace_globals_in(fSSA.globals_in,cs_globals_in,bindings_in,counter);
  get_replace_globals_in(fSSA.globals_in,*f_it,cs_globals_in,bindings_in,counter);

  //equalities for globals out (including unmodified globals)
  //bindings_out.push_back(get_replace_globals_out(SSA.globals_out,cs_globals_in,cs_globals_out));

  //get_replace_globals_out(fSSA.globals_out,cs_globals_in,cs_globals_out,bindings_out,counter);
  get_replace_globals_out(fSSA.globals_out,*f_it,cs_globals_in,cs_globals_out,bindings_out,counter);

}

/*******************************************************************\

Function: ssa_inlinert::get_summary

  Inputs:

 Outputs: 

 Purpose: get summary for function call

\*******************************************************************/

void ssa_inlinert::get_summary(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it, 
  const summaryt &summary,
  bool forward, 
  exprt::operandst &summaries,
  exprt::operandst &bindings,
  int counter,
  bool error_summ)
{
  //getting globals at call site
  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
  goto_programt::const_targett loc = n_it->location;
  if(forward) 
  {
    SSA.get_globals(loc,cs_globals_in);
    SSA.get_globals(loc,cs_globals_out,false);
  }
  else 
  {
    SSA.get_globals(loc,cs_globals_out);
    SSA.get_globals(loc,cs_globals_in,false);
  }

#if 0
  std::cout << "cs_globals_in: ";
  for(summaryt::var_sett::const_iterator it = cs_globals_in.begin();
      it != cs_globals_in.end(); it++)
    std::cout << from_expr(SSA.ns,"",*it) << " ";
  std::cout << std::endl;

  std::cout << "cs_globals_out: ";
  for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
      it != cs_globals_out.end(); it++)
    std::cout << from_expr(SSA.ns,"",*it) << " ";
  std::cout << std::endl;
#endif

  //equalities for arguments
  get_replace_params(SSA,summary.params,n_it,*f_it,bindings,counter);

  //equalities for globals_in
  if(forward){
    //get_replace_globals_in(summary.globals_in,cs_globals_in,bindings,counter);
    get_replace_globals_in(summary.globals_in,*f_it,cs_globals_in,bindings,counter);
  }
  else{
    //get_replace_globals_in(summary.globals_out,cs_globals_out,bindings,counter);
    get_replace_globals_in(summary.globals_out,*f_it,cs_globals_out,bindings,counter);
  }

  //constraints for transformer

  exprt transformer;

  if(error_summ)
    {
      // update transformer using the error_summaries map
      summaryt::call_sitet call_site(loc);
      summaryt::error_summariest::const_iterator e_it = 
	summary.error_summaries.find(call_site);
      if(e_it != summary.error_summaries.end() &&
	 !e_it->second.is_nil())
	transformer = e_it->second;
      else
	transformer = true_exprt();
    }
  else
    {
      if(forward)
	transformer = summary.fw_transformer.is_nil() ? true_exprt() : 
	  summary.fw_transformer;
      else 
	transformer = summary.bw_transformer.is_nil() ? true_exprt() : 
	  summary.bw_transformer;
    }
  
  rename(transformer,counter);
  summaries.push_back(implies_exprt(SSA.guard_symbol(n_it->location),
				    transformer));
  
  //equalities for globals out (including unmodified globals)
  if(forward){
    //get_replace_globals_out(summary.globals_out,cs_globals_in,cs_globals_out,bindings,counter);
    get_replace_globals_out(summary.globals_out,*f_it,cs_globals_in,cs_globals_out,bindings,counter);
  }
  else{
    //get_replace_globals_out(summary.globals_in,cs_globals_out,cs_globals_in,bindings,counter);
    get_replace_globals_out(summary.globals_in,*f_it,cs_globals_out,cs_globals_in,bindings,counter);
  }
}

/*******************************************************************\

Function: ssa_inlinert::get_summaries

  Inputs:

 Outputs: 

 Purpose: get summary for all function calls

\*******************************************************************/

exprt ssa_inlinert::get_summaries(const local_SSAt &SSA)
{
  exprt::operandst summaries,bindings;
  get_summaries(SSA,true,summaries,bindings);
  return and_exprt(conjunction(bindings),conjunction(summaries));
}

void ssa_inlinert::get_summaries(const local_SSAt &SSA,
				 bool forward,
				 exprt::operandst &summaries,
				 exprt::operandst &bindings)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname))
      {
	counter++;
        get_summary(SSA,n_it,f_it,summary_db.get(fname),
		    forward,summaries,bindings,counter);
      }
    }
  }
}

bool ssa_inlinert::get_summaries(const local_SSAt &SSA,
				 const summaryt::call_sitet &current_call_site,
				 bool forward,
				 exprt::operandst &assert_summaries,
				 exprt::operandst &noassert_summaries,
				 exprt::operandst &bindings)
{
  bool assertion_flag = false;
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
      {
	//do not use summary for current call site
	summaryt::call_sitet this_call_site(n_it->location);
	if(current_call_site == this_call_site)  
	  continue;

	assert(f_it->function().id()==ID_symbol); //no function pointers
	irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
	
        //TODO: we need a get_summary variant that retrieves the summary according the call_site from summary.error_summaries
	if(summary_db.exists(fname))
	  {
	    summaryt summary = summary_db.get(fname);
	    if(summary.has_assertion == true){
	      counter++;
	      get_summary(SSA,n_it,f_it,summary_db.get(fname),forward,assert_summaries,bindings,counter,true);
	      assertion_flag = true;
	    }
	    else{
	      counter++;
	      get_summary(SSA,n_it,f_it,summary_db.get(fname),forward,noassert_summaries,bindings,counter,true);
	    }
	  }
      }
  }
  return assertion_flag;
}


/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs: 

 Purpose: replaces function calls by summaries
          if available in the summary store
          and does nothing otherwise

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt &SSA,
			   bool forward,
			   bool preconditions_as_assertions,
			   int counter)
{
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname)) 
      {
        summaryt summary = summary_db.get(fname);

        status() << "Replacing function " << fname << " by summary" << eom;

	//getting globals at call site
	local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	goto_programt::const_targett loc = n_it->location;
	SSA.get_globals(loc,cs_globals_in);
	SSA.get_globals(loc,cs_globals_out,false);

        //replace
        replace(SSA,n_it,f_it,cs_globals_in,cs_globals_out,summary,
		forward,preconditions_as_assertions,counter);

        //remove function_call
        rm_function_calls.insert(f_it);
      }
      else debug() << "No summary available for function " << fname << eom;
      commit_node(n_it);
    }
    commit_nodes(SSA.nodes,n_it);
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs: 

 Purpose: replaces inlines functions 
          if SSA is available in functions
          and does nothing otherwise

\*******************************************************************/

/*
void ssa_inlinert::replace(local_SSAt &SSA,
			   const ssa_dbt &ssa_db, 
			   bool recursive, bool rename)
*/
void ssa_inlinert::replace(local_SSAt &SSA,
			   const ssa_dbt &ssa_db,
			   int counter,
			   bool recursive, bool rename)
{
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it != SSA.nodes.end(); n_it++)
    {
      for(local_SSAt::nodet::function_callst::iterator 
	    f_it = n_it->function_calls.begin();
	  f_it != n_it->function_calls.end(); f_it++)
	{
	  assert(f_it->function().id()==ID_symbol); //no function pointers
	  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
	  
	  if(ssa_db.exists(fname)) 
	    {
	      status() << "Inlining function " << fname << eom;
	      local_SSAt fSSA = ssa_db.get(fname); //copy
	      
	      if(rename)
		{
		  //getting globals at call site
		  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
		  goto_programt::const_targett loc = n_it->location;
		  SSA.get_globals(loc,cs_globals_in);
		  SSA.get_globals(loc,cs_globals_out,false);
		  
		  if(recursive)
		    {
		      replace(fSSA,ssa_db,true,counter);
		    }

		  //replace
		  replace(SSA.nodes,n_it,f_it,cs_globals_in,cs_globals_out,fSSA,counter);
		}
	      else // just add to nodes
		{
		  for(local_SSAt::nodest::const_iterator fn_it = fSSA.nodes.begin();
		      fn_it != fSSA.nodes.end(); fn_it++)
		    {
		      debug() << "new node: "; fn_it->output(debug(),fSSA.ns); 
		      debug() << eom;
		      
		      new_nodes.push_back(*fn_it);
		    }
		}
	    }
	  else debug() << "No body available for function " << fname << eom;
	  commit_node(n_it);
	}
      commit_nodes(SSA.nodes,n_it);
    }
}

/*******************************************************************\

Function: ssa_inlinert::replace()

  Inputs:

 Outputs:

 Purpose: inline summary

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt &SSA,
			   local_SSAt::nodest::iterator node, 
			   local_SSAt::nodet::function_callst::iterator f_it, 
			   const local_SSAt::var_sett &cs_globals_in,
			   const local_SSAt::var_sett &cs_globals_out, 
			   const summaryt &summary,
			   bool forward,
			   bool preconditions_as_assertions,
			   int counter)
{
  //equalities for arguments
  replace_params(summary.params,*f_it,counter);

  //equalities for globals_in
  replace_globals_in(summary.globals_in,cs_globals_in,counter);

  //constraints for precondition and transformer
  exprt precondition;
  if(forward) precondition = summary.fw_precondition;
  else precondition = summary.bw_precondition;
  if(!preconditions_as_assertions)
    {
      rename(precondition,counter);
      node->constraints.push_back(
				  implies_exprt(SSA.guard_symbol(node->location),
						precondition)); 
    }
  else
    {
      rename(precondition,counter);
      node->assertions.push_back(
				 implies_exprt(SSA.guard_symbol(node->location),
					       precondition));  
    }
  exprt transformer;
  if(forward) transformer = summary.fw_transformer;
  else transformer = summary.bw_transformer;
  node->constraints.push_back(transformer);  //copy
  exprt &_transformer = node->constraints.back();
  rename(_transformer,counter);
  
  //remove function call
  rm_function_calls.insert(f_it);

  //equalities for globals out (including unmodified globals)
  replace_globals_out(summary.globals_out,cs_globals_in,cs_globals_out,counter);
}

/*******************************************************************\

 Function: ssa_inlinert::replace()

 Inputs:

 Outputs:

 Purpose: inline function 

 Remark: local_SSAt::nodest maps a goto program target to a single SSA node,
         when inlining several calls to the same function 
         instructions appear factorized by the goto program targets 

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
			   local_SSAt::nodest::iterator node, 
			   local_SSAt::nodet::function_callst::iterator f_it, 
			   const local_SSAt::var_sett &cs_globals_in,
			   const local_SSAt::var_sett &cs_globals_out, 
			   const local_SSAt &function,
			   int counter)
{
  //equalities for arguments
  replace_params(function.params,*f_it,counter);

  //equalities for globals_in
  replace_globals_in(function.globals_in,cs_globals_in,counter);
  
  //add function body
  for(local_SSAt::nodest::const_iterator n_it = function.nodes.begin();
      n_it != function.nodes.end(); n_it++)
    {
    local_SSAt::nodet n = *n_it;  //copy
    rename(n,counter);
    new_nodes.push_back(n);
  }
 
  //remove function call
  rm_function_calls.insert(f_it);
  
  //equalities for globals out (including unmodified globals)
  replace_globals_out(function.globals_out,cs_globals_in,cs_globals_out,counter);
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_in()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::get_replace_globals_in(const local_SSAt::var_sett &globals_in,
					  const function_application_exprt &funapp_expr,
					  const local_SSAt::var_sett &globals,
					  exprt::operandst &c,
					  int counter)
{
  std::string suffix = id2string(funapp_expr.get(ID_suffix));

  //equalities for globals_in
  for(summaryt::var_sett::const_iterator it = globals_in.begin();
      it != globals_in.end(); it++)
    {
      symbol_exprt lhs = *it; //copy
      rename(lhs,counter);
      symbol_exprt rhs;
      if(find_corresponding_symbol(*it,globals,rhs))
	{
	  rhs.set_identifier(id2string(rhs.get_identifier())+suffix);
	  
	  debug() << "binding: " << lhs.get_identifier() << " == " 
		  << rhs.get_identifier() << eom;
	  c.push_back(equal_exprt(lhs,rhs));
	}
#if 0
      else
	warning() << "'" << it->get_identifier() 
		  << "' not bound in caller" << eom;
#endif
    }
  //return conjunction(c);
}

void ssa_inlinert::replace_globals_in(const local_SSAt::var_sett &globals_in, 
				      const local_SSAt::var_sett &globals,
				      int counter)
{
  //equalities for globals_in
  for(summaryt::var_sett::const_iterator it = globals_in.begin();
      it != globals_in.end(); it++)
  {
    symbol_exprt lhs = *it; //copy
    rename(lhs,counter);
    symbol_exprt rhs;
    if(find_corresponding_symbol(*it,globals,rhs))
      {
	debug() << "binding: " << lhs.get_identifier() << " == " 
		<< rhs.get_identifier() << eom;
	new_equs.push_back(equal_exprt(lhs,rhs));
      }
#if 0
    else
      warning() << "'" << it->get_identifier() 
                << "' not bound in caller" << eom;
#endif
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace_params()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::get_replace_params(const local_SSAt &SSA,
				      const local_SSAt::var_listt &params,
				      local_SSAt::nodest::const_iterator n_it,
				      const function_application_exprt &funapp_expr,
				      exprt::operandst &c,
				      int counter)
{
  //std::string suffix = id2string(funapp_expr.get(ID_suffix));

  //equalities for arguments
  local_SSAt::var_listt::const_iterator p_it = params.begin();
  for(exprt::operandst::const_iterator it = funapp_expr.arguments().begin();
      it != funapp_expr.arguments().end(); it++, p_it++)
    {
#if 0
      std::cout << "replace param " << from_expr(SSA.ns,"",*p_it)
	        << " == " << from_expr(SSA.ns,"",*it) << std::endl;
#endif
      
#if 0
      local_SSAt::var_listt::const_iterator next_p_it = p_it; 
      if(funapp_expr.arguments().size() != params.size() && 
	 ++next_p_it==params.end()) //TODO: handle ellipsis
	{
	  warning() << "ignoring excess function arguments" << eom; 
	  break;
	}
#endif

      if(SSA.ns.follow(it->type()).id()==ID_struct)
      {
        exprt rhs = SSA.read_rhs(*it, n_it->location); //copy
#if 0
	std::cout << "split param " << from_expr(SSA.ns,"",*it)
	        << " into " << from_expr(SSA.ns,"",rhs) << std::endl;
#endif
	forall_operands(o_it, rhs)
	{
	  assert(p_it!=params.end());
	  exprt lhs = *p_it; //copy
	  rename(lhs,counter);
#if 0
	  std::cout << "split replace param " << from_expr(SSA.ns,"",*p_it)
		    << " == " << from_expr(SSA.ns,"",*o_it) << std::endl;
#endif
          c.push_back(equal_exprt(lhs,*o_it));
	  ++p_it;
	}
      }
      else
      {
	exprt lhs = *p_it; //copy
	rename(lhs,counter);
        c.push_back(equal_exprt(lhs,*it));
        //symbol_exprt sexpr = to_symbol_expr(*it);
        //sexpr.set_identifier(id2string(sexpr.get_identifier())+suffix);
        //c.push_back(equal_exprt(lhs,sexpr));
      }
    }
}

void ssa_inlinert::replace_params(const local_SSAt::var_listt &params,
				  const function_application_exprt &funapp_expr,
				  int counter)
{
  //equalities for arguments
  local_SSAt::var_listt::const_iterator p_it = params.begin();
  for(exprt::operandst::const_iterator it = funapp_expr.arguments().begin();
      it != funapp_expr.arguments().end(); it++, p_it++)
    {
      local_SSAt::var_listt::const_iterator next_p_it = p_it; 
      if(funapp_expr.arguments().size() != params.size() && 
	 ++next_p_it==params.end()) //TODO: handle ellipsis
	{
	  warning() << "ignoring excess function arguments" << eom; 
	  break;
	}
      
      exprt lhs = *p_it; //copy
      rename(lhs,counter);
      new_equs.push_back(equal_exprt(lhs,*it));
    }
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_out()

  Inputs:

 Outputs:

 Purpose: equalities for globals out (including unmodified globals)

\*******************************************************************/

void ssa_inlinert::get_replace_globals_out(const local_SSAt::var_sett &globals_out,
					   const function_application_exprt &funapp_expr,
					   const local_SSAt::var_sett &cs_globals_in,  
					   const local_SSAt::var_sett &cs_globals_out,
					   exprt::operandst &c,
					   int counter)
{
  std::string suffix = id2string(funapp_expr.get(ID_suffix));
  
  //equalities for globals_out
  for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
      it != cs_globals_out.end(); it++)
    {
      symbol_exprt lhs = *it; //copy

      lhs.set_identifier(id2string(lhs.get_identifier())+suffix);

      symbol_exprt rhs;
      if(find_corresponding_symbol(*it,globals_out,rhs))
	rename(rhs,counter);
      else{
	bool found = find_corresponding_symbol(*it,cs_globals_in,rhs);
	assert(found);
	rhs.set_identifier(id2string(rhs.get_identifier())+suffix);
      }
      c.push_back(equal_exprt(lhs,rhs));
    }
}

void ssa_inlinert::replace_globals_out(const local_SSAt::var_sett &globals_out, 
				       const local_SSAt::var_sett &cs_globals_in,  
				       const local_SSAt::var_sett &cs_globals_out,
				       int counter)
{
  //equalities for globals_out
  for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
      it != cs_globals_out.end(); it++)
    {
      symbol_exprt rhs = *it; //copy
      symbol_exprt lhs;
      if(find_corresponding_symbol(*it,globals_out,lhs))
	rename(lhs,counter);
      else
	assert(find_corresponding_symbol(*it,cs_globals_in,lhs));
      new_equs.push_back(equal_exprt(lhs,rhs));
    }
}

/*******************************************************************\

Function: ssa_inlinert::havoc()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::function_callst::iterator f_it)
{
  //remove function call
  rm_function_calls.insert(f_it);
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt ssa_inlinert::rename(irep_idt &id, int counter)
{
  return id2string(id)+"@"+i2string(counter);
}


/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt ssa_inlinert::rename(irep_idt &id, int counter, bool attach){

  std::string id_str = id2string(id);

  if(attach == false){
    //find first @ where afterwards there are no letters
    size_t pos = std::string::npos;
    for(size_t i=0;i<id_str.size();i++)
      {
	char c = id_str.at(i);
	if(pos==std::string::npos)
	  {
	    if(c=='@')
	      pos = i;
	  }
	else
	  {
	    if(!('0'<=c && c<='9'))
	      pos = std::string::npos;
	  }
      }
    if(pos!=std::string::npos)
      return id_str.substr(0,pos);
    else
      return id_str;
  }
  else{
    if(id_str.find('@') != std::string::npos)
      return id;
    else
      return rename(id, counter);
  }
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(exprt &expr, int counter) 
{
  if(expr.id()==ID_symbol) 
    {
      symbol_exprt &sexpr = to_symbol_expr(expr);
      std::string id_str = id2string(sexpr.get_identifier());
      irep_idt id;

      if(id_str.find('@') != std::string::npos)
	id = id_str;
      else
	id = id_str+"@"+i2string(counter);
      
      sexpr.set_identifier(id);
    }
  for(exprt::operandst::iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
    {
      rename(*it,counter);
    }
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(local_SSAt::nodet &node, int counter) 
{
  for(local_SSAt::nodet::equalitiest::iterator e_it = node.equalities.begin();
      e_it != node.equalities.end(); e_it++)
    {
      rename(*e_it, counter);
    }
  for(local_SSAt::nodet::constraintst::iterator c_it = node.constraints.begin();
      c_it != node.constraints.end(); c_it++)
    {
      rename(*c_it, counter);
    }  
  for(local_SSAt::nodet::assertionst::iterator a_it = node.assertions.begin();
      a_it != node.assertions.end(); a_it++)
    {
      rename(*a_it, counter);
    }  
  for(local_SSAt::nodet::function_callst::iterator 
	f_it = node.function_calls.begin();
      f_it != node.function_calls.end(); f_it++)
    {
      rename(*f_it, counter);
    }  
}

/*******************************************************************\

Function: ssa_inlinert::rename_to_caller

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename_to_caller(
 local_SSAt::nodet::function_callst::const_iterator f_it, 
 const local_SSAt::var_listt &params, 
 const local_SSAt::var_sett &cs_globals_in, 
 const local_SSAt::var_sett &globals_in, 
 exprt &expr)
{
  assert(params.size()==f_it->arguments().size());

  replace_mapt replace_map;

  local_SSAt::var_listt::const_iterator p_it = params.begin();
  for(exprt::operandst::const_iterator it = f_it->arguments().begin();
      it !=  f_it->arguments().end(); it++, p_it++)
  {
    local_SSAt::var_listt::const_iterator next_p_it = p_it; 
    if(f_it->arguments().size() != params.size() && 
       ++next_p_it==params.end()) //TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom; 
      break;
    }
    replace_map[*p_it] = *it;
  }

  for(summaryt::var_sett::const_iterator it = globals_in.begin();
      it != globals_in.end(); it++)
  {
    symbol_exprt cg;
    if(find_corresponding_symbol(*it,cs_globals_in,cg))
      replace_map[*it] = cg;
    else 
    {
#if 0
      warning() << "'" << it->get_identifier() 
                << "' not bound in caller" << eom;
#endif
      replace_map[*it] = 
        symbol_exprt(id2string(it->get_identifier())+
        "@"+i2string(++counter),it->type());
    }
  }

  replace_expr(replace_map,expr);
}

/*******************************************************************\

Function: ssa_inlinert::rename_to_callee

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename_to_callee(
  local_SSAt::nodet::function_callst::const_iterator f_it, 
  const local_SSAt::var_listt &params, 
  const local_SSAt::var_sett &cs_globals_in, 
  const local_SSAt::var_sett &globals_in, 
  exprt &expr)
{
  replace_mapt replace_map;

  local_SSAt::var_listt::const_iterator p_it = params.begin();
  for(exprt::operandst::const_iterator it =  f_it->arguments().begin();
      it !=  f_it->arguments().end(); it++, p_it++)
  {
    local_SSAt::var_listt::const_iterator next_p_it = p_it; 
    if(f_it->arguments().size() != params.size() && 
       ++next_p_it==params.end()) //TODO: handle ellipsis
      {
	warning() << "ignoring excess function arguments" << eom; 
	break;
      }
    replace_map[*it] = *p_it;
  }

  /*  replace_expr(replace_map,expr);

  replace_map.clear(); //arguments might contain globals, 
                       // thus, we have to replace them separately
		       */
  for(summaryt::var_sett::const_iterator it = cs_globals_in.begin();
      it != cs_globals_in.end(); it++)
    {
      symbol_exprt cg;
      if(find_corresponding_symbol(*it,globals_in,cg))
	replace_map[*it] = cg;
      else
	{
#if 0
	  warning() << "'" << it->get_identifier() 
		    << "' not bound in caller" << eom;
#endif
	  replace_map[*it] =
	    symbol_exprt(id2string(it->get_identifier())+
			 "@"+i2string(++counter),it->type());
	}
    }
  
  replace_expr(replace_map,expr);
}

/*******************************************************************\

Function: ssa_inlinert::commit_node()

  Inputs:

 Outputs:

 Purpose: apply changes to node, must be called after replace and havoc
          (needed because replace and havoc usually called while 
           iterating over equalities,
           and hence we cannot modify them)

\*******************************************************************/

void ssa_inlinert::commit_node(local_SSAt::nodest::iterator node)
{
  //remove obsolete function calls
  for(std::set<local_SSAt::nodet::function_callst::iterator>::iterator 
      it = rm_function_calls.begin();
      it != rm_function_calls.end(); it++) 
  {
    node->function_calls.erase(*it);
  }
  rm_function_calls.clear();

  //insert new equalities
  node->equalities.insert(node->equalities.end(),
    new_equs.begin(),new_equs.end());
  new_equs.clear();
}

/*******************************************************************\

Function: ssa_inlinert::commit_nodes()

  Inputs:

 Outputs:

 Purpose: returns true if no nodes were to be committed

\*******************************************************************/

bool ssa_inlinert::commit_nodes(local_SSAt::nodest &nodes,
                                 local_SSAt::nodest::iterator n_pos)
{
  if(new_nodes.empty()) return true;
  nodes.splice(n_pos,new_nodes,new_nodes.begin(),new_nodes.end());
  return false;
}

/*******************************************************************\

Function: ssa_inlinert::find_corresponding_symbol

  Inputs:

 Outputs: returns false if the symbol is not found

 Purpose:

\*******************************************************************/

bool ssa_inlinert::find_corresponding_symbol(const symbol_exprt &s, 
					 const local_SSAt::var_sett &globals,
                                         symbol_exprt &s_found)
{
  const irep_idt &s_orig_id = get_original_identifier(s);
  for(local_SSAt::var_sett::const_iterator it = globals.begin();
      it != globals.end(); it++)
    {
#if 0
      std::cout << s_orig_id << " =?= " << get_original_identifier(*it) << std::endl;
#endif
      if(s_orig_id == get_original_identifier(*it))
	{
	  s_found = *it;
	  return true;
	}
    }
  return false;
}

/*******************************************************************\

Function: ssa_inlinert::get_original_identifier

  Inputs:

 Outputs: 

 Purpose: TODO: this is a potential source of bugs. Better way to do that?

\*******************************************************************/

irep_idt ssa_inlinert::get_original_identifier(const symbol_exprt &s)
{
  std::string id = id2string(s.get_identifier());

  //find first #@%!$ where afterwards there are no letters
  size_t pos = std::string::npos;
  for(size_t i=0;i<id.size();i++)
  {
    char c = id.at(i);
    if(pos==std::string::npos)
    {
      if(c=='#' || c=='@' || c=='%' || c=='!' || c=='$')
        pos = i;
    }
    else
    {
      if(!(c=='#' || c=='@' || c=='%' || c=='!' || c=='$') &&
         !(c=='p' || c=='h' || c=='i') &&
         !('0'<=c && c<='9'))
        pos = std::string::npos;
    }
  }
  if(pos!=std::string::npos) id = id.substr(0,pos);
  return id;
}

