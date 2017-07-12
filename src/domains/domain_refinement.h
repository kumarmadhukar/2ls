/*******************************************************************\

Module: Domain Refinement Interface

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DOMAIN_REFINEMENT_H
#define CPROVER_DOMAIN_REFINEMENT_H

#include "incremental_solver.h"
#include "template_generator_base.h"
#include "../ssa/local_SSA.h"

class domain_refinementt
{
public:
  explicit domain_refinementt(
    const local_SSAt &_SSA, 
    incremental_solvert &_solver) 
    :
    SSA(_SSA),
    solver(_solver)
    {}

  //refine, returns true if there are no more refinements 
  virtual bool operator()() { return true; }

  //template generators associated with this SSA and solver
  typedef std::map<irep_idt, template_generator_baset> template_generatorst;
  template_generatorst template_generators;

protected:
  const local_SSAt &SSA;
  incremental_solvert &solver;
};

#endif
