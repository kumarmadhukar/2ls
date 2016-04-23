/*******************************************************************\

Module: Storage for Function SSAs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_SSA_DB_H
#define CPROVER_LOCAL_SSA_DB_H

#include <util/options.h>

#include "../ssa/local_ssa.h"
#include "../ssa/unwindable_local_ssa.h"
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_dependency_graph.h"
#include "../domains/incremental_solver.h"
#include <goto-programs/goto_functions.h>

class ssa_inlinert;
class ssa_dependency_grapht;

class ssa_dbt
{
 public:
  typedef irep_idt function_namet;
  typedef std::map<function_namet, unwindable_local_SSAt*> functionst;
  typedef std::map<function_namet, ssa_dependency_grapht*> depgrapht;
  typedef std::map<function_namet, incremental_solvert*> solverst;

  explicit ssa_dbt(const optionst &_options) 
    : options(_options)
    { }
  
  ~ssa_dbt() 
  {
    for(functionst::iterator it = store.begin();
        it != store.end(); it++)
      delete it->second;
    for(solverst::iterator it = the_solvers.begin();
        it != the_solvers.end(); it++)
      delete it->second;
  }

  local_SSAt &get(const function_namet &function_name) const 
    { return *store.at(function_name); }

  ssa_dependency_grapht &get_depgraph(const function_namet &function_name) const 
    { return *depgraph_store.at(function_name); }

  incremental_solvert &get_solver(const function_namet &function_name)
  { 
    solverst::iterator it = the_solvers.find(function_name);
    if(it!=the_solvers.end()) return *(it->second);
    the_solvers[function_name] = 
      incremental_solvert::allocate(store.at(function_name)->ns,
				    options.get_bool_option("refine"));
    return *the_solvers.at(function_name); 
  }

  functionst &functions() { return store; }
  solverst &solvers() { return the_solvers; }

  bool exists(const function_namet &function_name) const  
    { return store.find(function_name)!=store.end(); }

  void create(const function_namet &function_name, 
              const goto_functionst::goto_functiont &goto_function,
              const namespacet &ns) 
  { 
    store[function_name] = new unwindable_local_SSAt(goto_function,ns);
  }

  void depgraph_create(const function_namet &function_name, const namespacet &ns, ssa_inlinert &ssa_inliner, bool entry);
  
 protected:
  const optionst &options;
  functionst store;
  depgrapht depgraph_store;
  solverst the_solvers;
};

#endif
