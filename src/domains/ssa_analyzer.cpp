/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <util/options.h>


#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
//#include "solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "strategy_solver_equality.h"
#include "strategy_solver_predabs.h"
#include "ssa_analyzer.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#define BINSEARCH_SOLVER strategy_solver_binsearcht(*static_cast<tpolyhedra_domaint *>(domain), solver, assertions_check, SSA.ns)
//#define BINSEARCH_SOLVER strategy_solver_binsearch2t(*static_cast<tpolyhedra_domaint *>(domain), solver, assertions_check, SSA.ns)
//#define BINSEARCH_SOLVER strategy_solver_binsearch3t(*static_cast<tpolyhedra_domaint *>(domain), solver, assertions_check, SSA, SSA.ns)

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs: true if the computation was not aborted due to 
            assertion_checks that did not pass
 Purpose:

\*******************************************************************/

bool ssa_analyzert::operator()(incremental_solvert &solver,
			       local_SSAt &SSA, 
                               const exprt &precondition,
			       template_generator_baset &template_generator,
                               bool check_assertions)
{
  if(SSA.goto_function.body.instructions.empty())
    return true;

  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  // add precondition (or conjunction of asssertion in backward analysis)
  solver << precondition;
  
  domain = template_generator.domain();

  // get assertions if check_assertions is requested
  literalt assertions_check = const_literal(false);
  bvt assertion_literals;
  if(check_assertions)
  {  
    exprt::operandst ll;
    for(local_SSAt::nodest::iterator n_it=SSA.nodes.begin();
	n_it!=SSA.nodes.end(); n_it++) 
    {
      assert(n_it->assertions.size()<=1);
      for(local_SSAt::nodet::assertionst::const_iterator
	    a_it=n_it->assertions.begin();
	  a_it!=n_it->assertions.end();
	  a_it++)
      {
	literalt l = solver.solver->convert(*a_it);
	assertion_literals.push_back(!l);
	ll.push_back(literal_exprt(!l));
	nonpassed_assertions.push_back(n_it);
      }
    }
    assertions_check = solver.solver->convert(disjunction(ll));
  }

  // get strategy solver from options
  strategy_solver_baset *strategy_solver;
  if(template_generator.options.get_bool_option("equalities"))
  {
    strategy_solver = new strategy_solver_equalityt(
      *static_cast<equality_domaint *>(domain), solver, 
      assertions_check, SSA.ns);    
    result = new equality_domaint::equ_valuet();
  }
  else
  {
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      result = new tpolyhedra_domaint::templ_valuet();
      strategy_solver = new strategy_solver_enumerationt(
        *static_cast<tpolyhedra_domaint *>(domain), solver, 
	assertions_check, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("predabs-solver"))
    {
      result = new predabs_domaint::templ_valuet();
      strategy_solver = new strategy_solver_predabst(
        *static_cast<predabs_domaint *>(domain), solver, 
	assertions_check, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      result = new tpolyhedra_domaint::templ_valuet();
      strategy_solver = new BINSEARCH_SOLVER;
    }
    else assert(false);
  }

  strategy_solver->set_message_handler(get_message_handler());

  unsigned iteration_number=0;

  // initialize domain
  domain->initialize(*result);

  strategy_solver_baset::progresst status;

  do
  {
    iteration_number++;
    
#ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
#endif
   
    status = strategy_solver->iterate(*result);

#ifdef DEBUG
    if(status == strategy_solver_baset::CHANGED) 
    {
      std::cout << "Value after " << iteration_number
            << " iteration(s):\n";
      domain->output_value(std::cout,*result,SSA.ns);
    }
#endif
  }
  while(status == strategy_solver_baset::CHANGED);

#ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  domain->output_value(std::cout,*result,SSA.ns);
#endif

  //get status of assertions
  if(!assertions_check.is_false() && 
     status == strategy_solver_baset::FAILED)
  {
    nonpassed_assertionst::iterator it = nonpassed_assertions.begin();
    for(unsigned i=0;i<assertion_literals.size(); ++i)
    {
      if(!solver.solver->l_get(assertion_literals[i]).is_true())
	nonpassed_assertions.erase(it++);
      else ++it;
    }
  }
  else nonpassed_assertions.clear();

  solver.pop_context();

  //statistics
  solver_calls += strategy_solver->get_number_of_solver_calls();
  solver_instances += strategy_solver->get_number_of_solver_instances();

  delete strategy_solver;

  return (status == strategy_solver_baset::CONVERGED);
}

/*******************************************************************\

Function: ssa_analyzert::get_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_result(exprt &_result, const domaint::var_sett &vars)
{
  domain->project_on_vars(*result,vars,_result);
}
