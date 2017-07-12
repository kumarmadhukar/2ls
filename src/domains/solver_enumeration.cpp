#include <iostream>

#include <util/simplify_expr.h>
#include "solver_enumeration.h"

bool solver_enumerationt::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv = 
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved = false;

  literalt activation_literal = new_context();

  exprt inv_expr = tpolyhedra_domain.to_pre_constraints(inv);
  debug() << "pre-inv: " << from_expr(ns,"",inv_expr) << eom;

#ifndef DEBUG_FORMULA
  solver << or_exprt(inv_expr, literal_exprt(activation_literal));
#else
  debug() << "literal " << activation_literal << eom;
  literalt l = solver.convert(or_exprt(inv_expr, literal_exprt(activation_literal)));
  if(!l.is_constant()) 
  {
    debug() << "literal " << l << ": " << from_expr(ns,"",or_exprt(inv_expr, literal_exprt(activation_literal))) <<eom;
    formula.push_back(l);
  }
#endif

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 

#ifndef DEBUG_FORMULA
  solver << or_exprt(disjunction(strategy_cond_exprs),
		     literal_exprt(activation_literal));
#else

  exprt expr_act=
    or_exprt(disjunction(strategy_cond_exprs),
	       literal_exprt(activation_literal));

  l = solver.convert(expr_act);
  if(!l.is_constant()) 
  {
    debug() << "literal " << l << ": " << 
      from_expr(ns,"", expr_act) <<eom;
    formula.push_back(l);
  }
#endif

  debug() << "solve(): ";

#ifdef DEBUG_FORMULA
  bvt whole_formula = formula;
  whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
  solver.set_assumptions(whole_formula);
#endif

  if(solve() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "SAT" << eom;
      
    #if 0
    for(unsigned i=0; i<whole_formula.size(); i++) 
    {
      debug() << "literal: " << whole_formula[i] << " " << 
        solver.l_get(whole_formula[i]) << eom;
    }
          
    for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
    {
      exprt c = tpolyhedra_domain.get_row_constraint(i,inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " << 
          from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.pre_guards[i]) << 
          " " << from_expr(ns, "", solver.get(tpolyhedra_domain.templ.pre_guards[i])) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.post_guards[i]) << " " 
          << from_expr(ns, "", solver.get(tpolyhedra_domain.templ.post_guards[i])) << eom; 	     	     }    
          
    for(replace_mapt::const_iterator
          it=renaming_map.begin();
          it!=renaming_map.end();    
          ++it)
          
    {
      debug() << "replace_map (1st): " << from_expr(ns, "", it->first) << " " << 
          from_expr(ns, "", solver.get(it->first)) << eom;
      debug() << "replace_map (2nd): " << from_expr(ns, "", it->second) << " " << 
          from_expr(ns, "", solver.get(it->second)) << eom;
    }
                  
    #endif
      
    tpolyhedra_domaint::templ_valuet new_value;
    tpolyhedra_domain.initialize(new_value);
    for(unsigned row=0;row<tpolyhedra_domain.template_size(); row++)
    {
      tpolyhedra_domaint::row_valuet v = 
	simplify_const(solver.get(strategy_value_exprs[row]));
      tpolyhedra_domain.set_row_value(row,v,new_value);

      debug() << "value: " << from_expr(ns,"",v) << eom;
    }
    tpolyhedra_domain.join(inv,new_value);

    improved = true;
  }
  else 
  {
    debug() << "UNSAT" << eom;

#ifdef DEBUG_FORMULA
    for(unsigned i=0; i<whole_formula.size(); i++) 
    {
      if(solver.is_in_conflict(whole_formula[i]))
        debug() << "is_in_conflict: " << whole_formula[i] << eom;
      else
        debug() << "not_in_conflict: " << whole_formula[i] << eom;
     }
#endif    
  }
  pop_context();

  return improved;
}
