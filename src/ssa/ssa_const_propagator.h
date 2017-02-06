/*******************************************************************\

Module: SSA Constant Propagator

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_CONST_PROPAGATOR_H
#define CPROVER_SSA_CONST_PROPAGATOR_H

#include <util/message.h>
#include <util/replace_symbol.h>

#include "local_ssa.h"

class ssa_const_propagatort : public messaget
{
 public:

  void operator()(std::list<exprt> &dest,
		  const local_SSAt &src);

  struct valuest
  {
  public:
    // maps variables to constants
    replace_symbolt replace_const;
    std::set<irep_idt> top_ids;

    void output(std::ostream &, const namespacet &) const;

    bool merge(const valuest &src);


    inline void clear()
    {
      replace_const.expr_map.clear();
      replace_const.type_map.clear();
      top_ids.clear();
    }

    bool empty() const
    {
      return replace_const.expr_map.empty() &&
        replace_const.type_map.empty() &&
        top_ids.empty();
    }

    void set_to(const exprt &lhs, const exprt &rhs_val);
    void set_to(const irep_idt &lhs_id, const exprt &rhs_val);

    bool maps_to_top(const exprt &expr) const;
    bool set_to_top(const exprt &expr);
    bool set_to_top(const irep_idt &id);
   
    bool iterate;

  };

  valuest values;

 protected:

  void assign(
	      valuest &dest,
	      const exprt &lhs,
	      exprt rhs,
	      const namespacet &ns) const;

  exprt evaluate_casts_in_constants(
				    exprt expr,
				    const typet& parent_type,
				    bool &valid) const;
  
  
  
};

#endif
