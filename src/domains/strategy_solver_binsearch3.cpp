#include <iostream>
#include <cassert>

#include <util/i2string.h>

#include "strategy_solver_binsearch3.h"
#include "util.h"


#define SUM_BOUND_VAR "sum_bound#"

//TODO: implement assertion check

strategy_solver_baset::progresst
strategy_solver_binsearch3t::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv = 
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  progresst progress = CONVERGED;

  solver.new_context(); //for improvement check

  exprt inv_expr = tpolyhedra_domain.to_pre_constraints(inv);

#if 0
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: " << from_expr(ns,"",inv_expr) << eom;
#endif

  solver << inv_expr;

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
#if 0
  debug() << "post-inv: ";
#endif
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
#if 0
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]);
#endif
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    //solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  debug() << eom;

  solver << disjunction(strategy_cond_exprs);

#if 0
  debug() << "solve(): ";
#endif

  std::set<tpolyhedra_domaint::rowt> improve_rows;
  std::map<tpolyhedra_domaint::rowt,symbol_exprt> symb_values;
  std::map<tpolyhedra_domaint::rowt,constant_exprt> lower_values;
  exprt::operandst blocking_constraint;
  bool improved_from_neginf = false;
  while(solver() == decision_proceduret::D_SATISFIABLE) //improvement check
  { 
#if 0
    debug() << "SAT" << eom;
#endif
    progress = CHANGED;

    unsigned row=0;  
    for(;row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true()) 
      {
#if 1
        debug() << "improve row " << row  << eom;
#endif
        improve_rows.insert(row);
	symb_values[row] = tpolyhedra_domain.get_row_symb_value(row);
	lower_values[row] =
          simplify_const(solver.get(strategy_value_exprs[row]));
	blocking_constraint.push_back(
          literal_exprt(!strategy_cond_literals[row]));
	if(tpolyhedra_domain.is_row_value_neginf(
               tpolyhedra_domain.get_row_value(row,inv)))
	  improved_from_neginf = true;
      }
    }
    solver << conjunction(blocking_constraint);
  }
  solver.pop_context(); //improvement check

  if(progress != CHANGED) //done
  {
#if 0
    debug() << "UNSAT" << eom;
#endif
    return progress;
  }

  //symbolic value system
  exprt pre_inv_expr = 
    tpolyhedra_domain.to_symb_pre_constraints(inv,improve_rows);
  exprt post_inv_expr = 
    tpolyhedra_domain.to_symb_post_constraints(improve_rows);

  assert(lower_values.size()>=1);
  std::map<tpolyhedra_domaint::rowt,symbol_exprt>::iterator 
    it = symb_values.begin();
  exprt _lower = lower_values[it->first];
#if 1
  debug() << "update row " << it->first << ": " 
	    << from_expr(ns,"",lower_values[it->first]) << eom;
#endif
  tpolyhedra_domain.set_row_value(it->first,lower_values[it->first],inv);
  exprt _upper = 
    tpolyhedra_domain.get_max_row_value(it->first);
  exprt sum = it->second;
  for(it++; it != symb_values.end(); it++)
  {
    sum = plus_exprt(sum,it->second);
    _upper = plus_exprt(_upper,tpolyhedra_domain.get_max_row_value(it->first));
    _lower = plus_exprt(_lower,lower_values[it->first]);

#if 1
    debug() << "update row " << it->first << ": " 
	    << from_expr(ns,"",lower_values[it->first]) << eom;
#endif
    tpolyhedra_domain.set_row_value(it->first,lower_values[it->first],inv);
  }
  
  //do not solve system if we have just reached a new loop (the system will be very large!)
  if(improved_from_neginf) return progress;

  solver.new_context(); //symbolic value system
  solver << pre_inv_expr;
  solver << post_inv_expr;

#if 1
  debug() << "symbolic value system: " << eom;
  debug() << "pre-inv: " << from_expr(ns,"",pre_inv_expr) << eom;
  debug() << "post-inv: " << from_expr(ns,"",post_inv_expr) << eom;
#endif

/*
  //add renamed SSA for rows 1..n-1
  SSA.unmark_nodes();
  for(unsigned i=1; i<symb_values.size(); i++)
  {
    exprt _pre_inv_expr = pre_inv_expr; //copy
    exprt _post_inv_expr = post_inv_expr; //copy
//    tpolyhedra_domain.rename_for_row(_pre_inv_expr,i);
//    tpolyhedra_domain.rename_for_row(_post_inv_expr,i);
    solver << _pre_inv_expr;
    solver << _post_inv_expr;

#if 1
  debug() << "pre-inv " << i << ": " << from_expr(ns,"",_pre_inv_expr) << eom;
  debug() << "post-inv " << i << ": " << from_expr(ns,"",_post_inv_expr) << eom;
#endif

    //TODO: this must be the full SSA, even with incremental unwinding!
    std::list<exprt> program;
    program  << SSA;
    for(std::list<exprt>::iterator it = program.begin();
	it != program.end(); it++)
    {
//      tpolyhedra_domain.rename_for_row(*it,i);
#if 1
      debug() << "ssa " << i << ": " << from_expr(ns,"",*it) << eom;
#endif
    }
    solver << SSA;
  }
  SSA.mark_nodes();
*/
  extend_expr_types(sum);
  extend_expr_types(_upper);
  extend_expr_types(_lower);
  tpolyhedra_domaint::row_valuet upper = simplify_const(_upper);
  tpolyhedra_domaint::row_valuet lower = simplify_const(_lower);
  assert(sum.type()==upper.type());
  assert(sum.type()==lower.type());

  symbol_exprt sum_bound(SUM_BOUND_VAR+i2string(sum_bound_counter++),sum.type());
  solver << equal_exprt(sum_bound,sum);

#if 1
  debug() << from_expr(ns,"",equal_exprt(sum_bound,sum)) << eom;
#endif

  while(tpolyhedra_domain.less_than(lower,upper))   
  {
      tpolyhedra_domaint::row_valuet middle = 
	tpolyhedra_domain.between(lower,upper);
      if(!tpolyhedra_domain.less_than(lower,middle)) middle = upper;

      // row_symb_value >= middle
      assert(sum_bound.type()==middle.type());
      exprt c = binary_relation_exprt(sum_bound,ID_ge,middle);

#if 1
      debug() << "upper: " << from_expr(ns,"",upper) << eom;
      debug() << "middle: " << from_expr(ns,"",middle) << eom;
      debug() << "lower: " << from_expr(ns,"",lower) << eom;
#endif

      solver.new_context(); // binary search iteration

#if 1
      debug() << "constraint: " << from_expr(ns, "", c) << eom;
#endif

      solver << c; 

      if(solver() == decision_proceduret::D_SATISFIABLE) 
	{ 
#if 0
	  debug() << "SAT" << eom;
#endif
     
	  lower = middle;

	  for(std::map<tpolyhedra_domaint::rowt,symbol_exprt>::iterator 
		it = symb_values.begin(); it != symb_values.end(); it++)
	  { 
#if 1
	    debug() << "update row " << it->first << " " 
		    << from_expr(ns,"",it->second) << ": ";
#endif
	    constant_exprt lower_row = 
              simplify_const(solver.get(it->second));
#if 1
	    debug() << from_expr(ns,"",lower_row) << eom;
#endif
	    tpolyhedra_domain.set_row_value(it->first,lower_row,inv);
	  }
	}
      else 
	{
#if 0
	  debug() << "UNSAT" << eom;
#endif

	  if(!tpolyhedra_domain.less_than(middle,upper)) middle = lower;

	  upper = middle;
	}
      solver.pop_context(); // binary search iteration
    }   

  solver.pop_context();  //symbolic value system


  return progress;
}
