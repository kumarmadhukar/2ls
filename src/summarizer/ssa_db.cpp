/*******************************************************************\

Module: Storage for Function SSAs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_db.h"

//void ssa_dbt::depgraph_create(const function_namet &function_name, const namespacet &ns, ssa_inlinert &ssa_inliner)
void ssa_dbt::depgraph_create(const function_namet &function_name, const namespacet &ns, ssa_inlinert &ssa_inliner, bool entry)
{
  depgraph_store[function_name] = new ssa_dependency_grapht(*this,ns);
  const local_SSAt &SSA=this->get(function_name);                                                                       
  depgraph_store[function_name]->create(SSA, ssa_inliner, entry);
}

