/*******************************************************************\

Module: Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARY_H
#define CPROVER_DELTACHECK_SUMMARY_H

#include <climits>
#include <iostream>
#include <set>

#include <util/std_expr.h>
#include "../ssa/local_ssa.h"

class summaryt
{
 public:
  typedef exprt predicatet;

  typedef std::list<symbol_exprt> var_listt;
  typedef std::set<symbol_exprt> var_sett;

  summaryt() : 
    fw_precondition(nil_exprt()), 
    fw_transformer(nil_exprt()), 
    fw_invariant(nil_exprt()), 
    bw_precondition(nil_exprt()), 
    bw_postcondition(nil_exprt()), 
    bw_transformer(nil_exprt()), 
    bw_invariant(nil_exprt()),
    mark_recompute(false),
    has_assertion(false) {}

  var_listt params;
  var_sett globals_in, globals_out;

 
  predicatet fw_precondition; // accumulated calling contexts (over-approx)
  //  predicatet fw_postcondition; // we are not projecting that out currently
  predicatet fw_transformer; // forward summary (over-approx)
  predicatet fw_invariant; // forward invariant (over-approx)
  predicatet bw_precondition; // accumulated preconditions (over- or under-approx)
  predicatet bw_postcondition; // accumulated postconditions (over- or under-approx)
  predicatet bw_transformer; // backward summary (over- or under-approx)
  predicatet bw_invariant; // backward invariant (over- or under-approx)

  bool mark_recompute; //to force recomputation of the summary
                       // (used for invariant reuse in k-induction)

  //--------------
  // the following is for generating interprocedural counterexample

  bool has_assertion; 

  std::list<local_SSAt::nodest::const_iterator> nonpassed_assertions;

  struct call_sitet { //TODO: we also need unwinding information here 
    call_sitet() 
      : location_number(UINT_MAX) {}
    explicit call_sitet(local_SSAt::locationt loc) 
      : location_number(loc->location_number) {}
    unsigned location_number;

    bool operator<(const call_sitet &other) const
      { return (location_number < other.location_number); }
    bool operator==(const call_sitet &other) const
      { return (location_number == other.location_number); }
  };

  const static call_sitet entry_call_site;
  typedef std::map<call_sitet, predicatet> error_summariest;
  error_summariest error_summaries;
  //--------------

  void output(std::ostream &out, const namespacet &ns) const;

  void join(const summaryt &new_summary);

 protected:

  void combine_or(exprt &olde, const exprt &newe);
  void combine_and(exprt &olde, const exprt &newe);

};



#endif
