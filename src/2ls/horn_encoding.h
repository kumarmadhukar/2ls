/*******************************************************************\

Module: Horn-clause Encoding

Author:

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_HORN_ENCODING_H
#define CPROVER_2LS_2LS_HORN_ENCODING_H

#include <iosfwd>

#include <goto-programs/goto_model.h>

void horn_encoding(
  const goto_modelt &,
  std::ostream &out);

#endif
