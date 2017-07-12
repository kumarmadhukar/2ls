/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/std_expr.h>

#include "data_flow.h"

/*******************************************************************\

Function: data_flowt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt data_flowt::rename(
  kindt kind,
  const exprt &src,
  goto_programt::const_targett t)
{
  exprt tmp=src;
  
  if(tmp.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(tmp).get_identifier();
    irep_idt new_identifier=
      id2string(identifier)+"#"+i2string(t->location_number)+"v"+i2string(version)+
      (kind==OUT?"O":kind==OUT_TAKEN?"Ot":"I");
    to_symbol_expr(tmp).set_identifier(new_identifier);
  }
  else
  {
    Forall_operands(it, tmp)
      *it=rename(kind, *it, t);
  }
  
  return tmp;
}

/*******************************************************************\

Function: data_flowt::guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt data_flowt::guard(goto_programt::const_targett t)
{
  irep_idt id=
    "data_flow::\\guard"+i2string(t->location_number)+"v"+i2string(version);
  return symbol_exprt(id, bool_typet());
}

/*******************************************************************\

Function: data_flowt::out_is_in

  Inputs:

 Outputs:

 Purpose: adds the skip transformer for location t

\*******************************************************************/

void data_flowt::out_is_in(goto_programt::const_targett t)
{
  // this says that v_OUT = v_IN
  for(objectst::const_iterator
      o_it=objects.begin();
      o_it!=objects.end();
      o_it++)
    solver.set_equal(rename(OUT, *o_it, t), rename(IN, *o_it, t));
}

/*******************************************************************\

Function: data_flowt::transformer

  Inputs:

 Outputs:

 Purpose: adds the transformer for location t

\*******************************************************************/

void data_flowt::transformer(goto_programt::const_targett t)
{
  if(t->is_assign())
  {
    const code_assignt &assignment=to_code_assign(t->code);
    
    std::set<exprt> assigned;
    
    if(assignment.lhs().id()==ID_symbol)
    {
      const exprt &lhs=assignment.lhs();
      const exprt &rhs=assignment.rhs();
      assigned.insert(lhs);
      solver.set_equal(rename(OUT, lhs, t), rename(IN, rhs, t));
    }

    for(objectst::const_iterator
        o_it=objects.begin();
        o_it!=objects.end();
        o_it++)
      if(assigned.find(*o_it)!=assigned.end())
        solver.set_equal(rename(OUT, *o_it, t), rename(IN, *o_it, t));
  }
  else if(t->is_assert())
  {
    //if(assert_to_assume)
    //  solver.set_to_true(rename(OUT, t->guard, t));

    out_is_in(t);
  }
  else if(t->is_function_call())
  {
    const code_function_callt &function_call=
      to_code_function_call(t->code);
    
    std::set<exprt> assigned;
    
    if(function_call.lhs().id()==ID_symbol)
    {
      const exprt &lhs=function_call.lhs();
      assigned.insert(lhs);
    }

    for(objectst::const_iterator
        o_it=objects.begin();
        o_it!=objects.end();
        o_it++)
      if(assigned.find(*o_it)!=assigned.end())
        solver.set_equal(rename(OUT, *o_it, t), rename(IN, *o_it, t));
  }
  else
    out_is_in(t);

  // Do guard. This is the OR of the incoming edges.
//  for(
  
}

/*******************************************************************\

Function: data_flowt::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_flowt::collect_objects(const exprt &src)
{
  forall_operands(it, src)
    collect_objects(*it);
  
  if(src.id()==ID_symbol)
    objects.insert(src);
}

/*******************************************************************\

Function: data_flowt::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_flowt::collect_objects(const goto_programt &goto_program)
{
  forall_goto_program_instructions(it, goto_program)
  {
    collect_objects(it->guard);
    collect_objects(it->code);
  }
}

/*******************************************************************\

Function: data_flowt::join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool data_flowt::join(goto_programt::const_targett t)
{
  // find facts that are true at all predecessors of t
  // and make them true at t

  // build 'in' vector
  solvert::var_sett in;
  in.reserve(objects.size());
  
  for(objectst::const_iterator
      o_it=objects.begin();
      o_it!=objects.end();
      o_it++)
  {
    in.push_back(rename(IN, *o_it, t));
  }
  
  // build list of matching 'out' vectors
  std::list<solvert::var_sett> src;

  const loct &loc=loc_map[t];
  for(goto_programt::const_targetst::const_iterator
      s_it=loc.succ.begin(); s_it!=loc.succ.end(); s_it++)
  {
    goto_programt::const_targett succ=*s_it;
    goto_programt::const_targett succ_next=*s_it;
    succ_next++;
    
    src.push_back(solvert::var_sett());
    solvert::var_sett &out=src.back();
    out.reserve(objects.size());

    // connect branches to correct output
    kindt kind=
      (succ->is_goto() && succ_next!=t)?OUT_TAKEN:OUT;

    for(objectst::const_iterator
        o_it=objects.begin();
        o_it!=objects.end();
        o_it++)
    {
      out.push_back(rename(kind, *o_it, succ));
    }
    
  }

  return solver.join(src, in);
}

/*******************************************************************\

Function: data_flowt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_flowt::operator()(const goto_programt &goto_program)
{
  // collect objects to track
  collect_objects(goto_program);
  
  // collect locations
  forall_goto_program_instructions(it, goto_program)
  {
    loct &loc=loc_map[it];
    
    // build successors
    goto_program.get_successors(it, loc.succ);

    // build predecessors
    for(goto_programt::const_targetst::const_iterator
        s_it=loc.succ.begin(); s_it!=loc.succ.end(); s_it++)
      loc_map[*s_it].pred.push_back(it);
  }  
  
  // add the transformers for all instructions
  forall_goto_program_instructions(it, goto_program)
    transformer(it);

  // now do data flow equations
  forall_goto_program_instructions(it, goto_program)
    work_queue.push_back(it);

  while(!work_queue.empty())
  {
    goto_programt::const_targett t=work_queue.back();
    work_queue.pop_back();

    if(join(t))
    {
      const loct &loc=loc_map[t];
      for(goto_programt::const_targetst::const_iterator
          s_it=loc.succ.begin(); s_it!=loc.succ.end(); s_it++)
        work_queue.push_back(*s_it);
    }
  }
}
