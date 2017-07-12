/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"
#include "template_generator_base.h"

class ssa_analyzert : public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_analyzert()
    : 
    result(NULL),
    solver_instances(0),
    solver_calls(0)
    {
    }  

    ~ssa_analyzert() 
    {
      if(result!=NULL) delete result;
    }

  // returns true if the computation was not aborted due to 
  //   assertion_checks that did not pass
  bool operator()(incremental_solvert &solver,
		  local_SSAt &SSA, 
                  const exprt &precondition,
		  template_generator_baset &template_generator,
                  bool check_assertions=false);

  //retrieve the result if operator() returned true
  void get_result(exprt &result, const domaint::var_sett &vars);

  //retrieve the non-passed assertions if operator() returned false
  typedef std::list<local_SSAt::nodest::const_iterator> 
    nonpassed_assertionst;
  nonpassed_assertionst get_nonpassed_assertions() 
    { return nonpassed_assertions; }

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  domaint *domain; //template generator is responsable for the domain object
  domaint::valuet *result;
  nonpassed_assertionst nonpassed_assertions;

  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
};


#endif
 
