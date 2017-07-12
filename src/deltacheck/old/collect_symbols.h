/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_COLLECT_SYMBOLS_H
#define CPROVER_DELTACHECK_COLLECT_SYMBOLS_H

#include <util/find_symbols.h>

#include <goto-programs/goto_functions.h>

void collect_symbols(
  const goto_functionst::goto_functiont &,
  find_symbols_sett &);

#endif
