/*******************************************************************\

Module: Show the overview for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTAGIT_REVISIONS_REPORT_H
#define CPROVER_DELTAGIT_REVISIONS_REPORT_H

void revisions_report(
  bool partial_html,
  const std::string &rel_path,
  unsigned max_revs);

#endif
