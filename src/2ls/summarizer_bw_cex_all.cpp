/*******************************************************************\

Module: Counterexample-based Backward Analysis 

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_bw_cex_all.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizer_bw_cex_allt::summarize()

  Inputs:

 Outputs:

 Purpose: calls multiple strategies

\*******************************************************************/

void summarizer_bw_cex_allt::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis (all)..." << eom;
  error_assertion = _error_assertion;

  summarizer_bw_cex_concrete.summarize(error_assertion);
  result = summarizer_bw_cex_concrete.check();

  if(result == property_checkert::UNKNOWN)
  {
    summarizer_bw_cex_ai.summarize(error_assertion);
    result = summarizer_bw_cex_ai.check();

    if(result == property_checkert::UNKNOWN)
    {
      summarizer_bw_cex_complete.summarize(error_assertion);
      result = summarizer_bw_cex_complete.check();
    }
  }
}

/*******************************************************************\

Function: summarizer_bw_cex_allt::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_allt::check()
{
  return result;
}
