/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GET_FUNCTION_H
#define CPROVER_GET_FUNCTION_H

#include <util/message.h>
#include <goto-programs/goto_model.h>

#include "index.h"

class get_functiont:public messaget
{
public:
  explicit get_functiont(const indext &_index):
    index(_index), ns(goto_model.symbol_table)
  {
  }

  goto_functionst::goto_functiont * operator()(
    const irep_idt &function_id);
  
  inline irep_idt get_file_name() const
  {
    return current_file_name;
  }
    
protected:
  const indext &index;
  irep_idt current_file_name;
  goto_modelt goto_model;

public:
  const namespacet ns;
};

#endif
