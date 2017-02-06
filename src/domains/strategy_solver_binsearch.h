#ifndef CPROVER_STRATEGY_SOLVER_BINSEARCH_H 
#define CPROVER_STRATEGY_SOLVER_BINSEARCH_H 

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearcht : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_binsearcht(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver, 
    literalt _assertion_check,
    const namespacet &_ns) : 
  strategy_solver_baset(_solver, _assertion_check, _ns),
  tpolyhedra_domain(_tpolyhedra_domain) {}

  virtual progresst iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;

};

#endif
