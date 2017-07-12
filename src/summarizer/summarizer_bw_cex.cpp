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

#include "summarizer_bw_cex.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_baset::summarize()
{
  assert(false); //unused
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_bw_cex_baset::summarize(const function_namet &function_name)
{
  exprt postcondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  compute_summary_rec(function_name,postcondition,true);
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_baset::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis..." << eom;
  error_assertion = _error_assertion;

  summarize(entry_function);
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::check()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_baset::check()
{
  assert(false);
}
