/*******************************************************************\

Module: SSA Constant Propagator

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <util/string2int.h>

#include "ssa_const_propagator.h"


//bool iterate = true;


/*******************************************************************\

Function: ssa_const_propagatort::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_const_propagatort::operator()(std::list<exprt> &dest,
			     const local_SSAt &src) 
{
  values.iterate = true;
  while(values.iterate){
    values.iterate = false;
    for(local_SSAt::nodest::const_iterator n_it = src.nodes.begin();
	n_it != src.nodes.end(); n_it++)
      {
	const local_SSAt::nodet &node=*n_it;
	
	// check if node is active; 'continue' if not active
	if(!node.enabling_expr.is_true())
	  continue;

	// if src.enabling_exprs does not have a true in the end, then also continue
	if(src.enabling_exprs.size() > 0)
	  if((src.enabling_exprs.back()).is_true())
	    continue;
	
	for(local_SSAt::nodet::equalitiest::const_iterator e_it=node.equalities.begin();
	    e_it!=node.equalities.end(); e_it++)
	  {
	    equal_exprt e = to_equal_expr(*e_it);
	    const exprt &lhs = e.lhs();
	    exprt &temprhs = e.rhs();
	    
	    // resolving conditional expressions
	    while(temprhs.id() == ID_if){
	      exprt simp_guard;
#ifdef DEBUG
	      std::cout << "guard:      " << from_expr(src.ns, "", temprhs.op0()) << std::endl;
#endif
	      simp_guard = simplify_expr(temprhs.op0(), src.ns);
#ifdef DEBUG
	      std::cout << "simplified: " << from_expr(src.ns, "", simp_guard) << std::endl;
#endif
	      if(simp_guard.is_true())
		temprhs = temprhs.op1();
	      else if(simp_guard.is_false())
		temprhs = temprhs.op2();
	      else
		break;
	    }
	    
	    const exprt &rhs = temprhs;
	    valuest copy_values = values;
	    
	    if(!copy_values.maps_to_top(rhs))
	      assign(copy_values,lhs,rhs,src.ns);
	    else
	      copy_values.set_to_top(lhs);
	    
#ifdef DEBUG
	    copy_values.output(std::cout,src.ns);
#endif
	    
	    if(rhs.id() == ID_symbol){ 
	      if(!values.maps_to_top(lhs))
		assign(values,rhs,lhs,src.ns);
	      else
		values.set_to_top(rhs);
	    }
	    
#ifdef DEBUG
	    values.output(std::cout,src.ns);
#endif
	    
	    values.merge(copy_values);
	    
#ifdef DEBUG
	    values.output(std::cout,src.ns);
#endif
	  }
	
	for(local_SSAt::nodet::constraintst::const_iterator c_it=n_it->constraints.begin();
	    c_it!=n_it->constraints.end(); c_it++)
	  {
	    if(c_it->id()!=ID_equal)
	      continue;
	    
	    const equal_exprt e = to_equal_expr(*c_it);
	    const exprt &lhs = e.lhs();
	    const exprt &rhs = e.rhs();

	    // if lhs is a variable and rhs is a constant expression
	    
	    valuest copy_values = values;

            if(!copy_values.maps_to_top(rhs))
              assign(copy_values,lhs,rhs,src.ns);
            else
              copy_values.set_to_top(lhs);

#ifdef DEBUG
            copy_values.output(std::cout,src.ns);
#endif
	    
	    // if rhs is a variable and lhs is a constant expression
	    
	    if(!values.maps_to_top(lhs))
	      assign(values,rhs,lhs,src.ns);
	    else
	      values.set_to_top(rhs);
	    
#ifdef DEBUG
            values.output(std::cout,src.ns);
#endif

            values.merge(copy_values);

#ifdef DEBUG
            values.output(std::cout,src.ns);
#endif
	    
	  }
      }
  }
  
#ifdef DEBUG
  values.output(std::cout,src.ns);
#endif
    
  // iterate over values and get all equalities
  for(replace_symbolt::expr_mapt::const_iterator
        it=values.replace_const.expr_map.begin();
      it!=values.replace_const.expr_map.end();
      ++it){
    
    //std::cout << ' ' << it->first << " = " <<
    //  from_expr(src.ns, "", it->second) << std::endl;

    dest.push_back(equal_exprt(symbol_exprt(it->first,it->second.type()),it->second));
    
  }
}

bool ssa_const_propagatort::valuest::maps_to_top(const exprt &expr) const
{
  find_symbols_sett symbols;
  find_symbols(expr,symbols);
  for(find_symbols_sett::const_iterator it = symbols.begin();
      it != symbols.end(); ++it)
    {
      if(replace_const.expr_map.find(*it)
	 == replace_const.expr_map.end())
	return true;
    }
  return false;
}


void ssa_const_propagatort::assign(
				   valuest &dest,
				   const exprt &lhs,
				   exprt rhs,
				   const namespacet &ns) const
{
#ifdef DEBUG
  std::cout << "assign:     " << from_expr(ns, "", lhs)
            << " := " << from_expr(ns, "", rhs) << std::endl;
#endif
 
  values.replace_const(rhs);

#ifdef DEBUG
  std::cout << "replace:    " << from_expr(ns, "", lhs)
            << " := " << from_expr(ns, "", rhs) << std::endl;
#endif

  rhs = simplify_expr(rhs,ns);

#ifdef DEBUG
  std::cout << "simplified: " << from_expr(ns, "", lhs)
            << " := " << from_expr(ns, "", rhs) << std::endl;
#endif

  dest.set_to(lhs,rhs);
}

bool ssa_const_propagatort::valuest::set_to_top(const irep_idt &id)
{
  bool result = false;
  replace_symbolt::expr_mapt::iterator r_it =
    replace_const.expr_map.find(id);
  if(r_it != replace_const.expr_map.end())
    {
      replace_const.expr_map.erase(r_it);
      result = true;
    }
  if(top_ids.find(id)==top_ids.end())
    {
      top_ids.insert(id);
      result = true;
    }
  return result;
}

bool ssa_const_propagatort::valuest::set_to_top(const exprt &expr)
{
  return set_to_top(to_symbol_expr(expr).get_identifier());
}

void ssa_const_propagatort::valuest::set_to(const irep_idt &lhs_id,
					       const exprt &rhs_val)
{
  
  if(replace_const.expr_map[lhs_id] != rhs_val){
    replace_const.expr_map[lhs_id] = rhs_val;
    iterate = true;
  }
  std::set<irep_idt>::iterator it = top_ids.find(lhs_id);
  if(it!=top_ids.end()) top_ids.erase(it);
}

void ssa_const_propagatort::valuest::set_to(const exprt &lhs,
					       const exprt &rhs_val)
{
  const irep_idt &lhs_id = to_symbol_expr(lhs).get_identifier();
  set_to(lhs_id,rhs_val);
}

void ssa_const_propagatort::valuest::output(
					       std::ostream &out,
					       const namespacet &ns) const
{
  out << "const map: " << std::endl;
  for(replace_symbolt::expr_mapt::const_iterator
        it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ++it)
    out << ' ' << it->first << "=" <<
      from_expr(ns, "", it->second) << std::endl;
  out << "top ids: " << std::endl;
  for(std::set<irep_idt>::const_iterator
        it=top_ids.begin();
      it!=top_ids.end();
      ++it)
    out << ' ' << *it << std::endl;
}

bool ssa_const_propagatort::valuest::merge(const valuest &src)
{
  bool changed = false;
  for(replace_symbolt::expr_mapt::const_iterator
        it=src.replace_const.expr_map.begin();
      it!=src.replace_const.expr_map.end(); ++it)
    {
      replace_symbolt::expr_mapt::iterator
	c_it = replace_const.expr_map.find(it->first);
      if(c_it != replace_const.expr_map.end())
	{
	  if(c_it->second != it->second)
	    {
	      set_to_top(it->first);
	      changed = true;
	    }
	}
      else if(top_ids.find(it->first)==top_ids.end())
	{
	  set_to(it->first,it->second);
	  changed = true;
	}
    }

  return changed;
}

