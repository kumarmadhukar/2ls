/*******************************************************************\


Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/threeval.h>
#include <solvers/prop/literal_expr.h>

#include "cover_goals_ext.h"

/*******************************************************************\

Function: cover_goals_extt::~cover_goals_extt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cover_goals_extt::~cover_goals_extt()
{
}

/*******************************************************************\

Function: cover_goals_extt::mark

  Inputs:

 Outputs:

 Purpose: Mark goals that are covered

\*******************************************************************/

void cover_goals_extt::mark()
{
  for(std::list<cover_goalt>::iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered &&
       solver.l_get(g_it->condition).is_true())
    {
      g_it->covered=true;
      _number_covered++;
    }
}
  
/*******************************************************************\

Function: cover_goals_extt::constaint

  Inputs:

 Outputs:

 Purpose: Build clause

\*******************************************************************/

void cover_goals_extt::constraint()
{
  exprt::operandst disjuncts;

  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered && !g_it->condition.is_false())
      disjuncts.push_back(literal_exprt(g_it->condition));

  // this is 'false' if there are no disjuncts
  solver << disjunction(disjuncts);
}

/*******************************************************************\

Function: cover_goals_extt::freeze_goal_variables

  Inputs:

 Outputs:

 Purpose: Build clause

\*******************************************************************/

void cover_goals_extt::freeze_goal_variables()
{
  for(std::list<cover_goalt>::const_iterator
      g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->condition.is_constant())
      solver.solver->set_frozen(g_it->condition);
}

/*******************************************************************\

Function: cover_goals_extt::operator()

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void cover_goals_extt::operator()()
{
  _iterations=_number_covered=0;
  
  decision_proceduret::resultt dec_result;
  
  // We use incremental solving, so need to freeze some variables
  // to prevent them from being eliminated.      
  freeze_goal_variables();

  do
  {
    // We want (at least) one of the remaining goals, please!
    _iterations++;
    
    constraint();
    
    dec_result = solver();

    switch(dec_result)
    {
    case decision_proceduret::D_UNSATISFIABLE: // DONE
      break;

    case decision_proceduret::D_SATISFIABLE:
      // mark the goals we got
      mark(); 
      
      // notify
      assignment();

      if(!all_properties) return; //exit on first failure if requested
      break;

    default:
      error() << "decision procedure has failed" << eom;
      return;
    }
  }
  while(dec_result==decision_proceduret::D_SATISFIABLE &&
        number_covered()<size());
}

/*******************************************************************\

Function: cover_goals_extt::assignment

  Inputs:

 Outputs:

 Purpose: checks whether a countermodel is spurious

\*******************************************************************/

void cover_goals_extt::assignment()
{
  std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=goals.begin();
  for(goal_mapt::const_iterator it=goal_map.begin();
      it!=goal_map.end(); it++, g_it++)
    {
      if(property_map[it->first].result==property_checkert::UNKNOWN &&
	 solver.l_get(g_it->condition).is_true())
	{
	  if(spurious_check)
	    {
	      assert((g_it->cond_expression).id() == ID_not);
	      exprt conjunct_expr = (g_it->cond_expression).op0();
	      
	      if(conjunct_expr.id() != ID_and)
              {
		solver.pop_context(); //otherwise this would interfere with necessary preconditions
		summarizer_bw_cex.summarize(g_it->cond_expression);
		property_map[it->first].result = summarizer_bw_cex.check();
		solver.new_context();
	      }
	      else
              {
		exprt::operandst failed_exprs;
		for(exprt::operandst::const_iterator c_it = 
		      conjunct_expr.operands().begin();
		    c_it != conjunct_expr.operands().end(); c_it++)
                {
		  literalt conjunct_literal = solver.convert(*c_it);
		  if(solver.l_get(conjunct_literal).is_false())
		    failed_exprs.push_back(*c_it);
		}
		solver.pop_context(); //otherwise this would interfere with necessary preconditions
		for(unsigned i=0; i<failed_exprs.size(); ++i)
		{
		  summarizer_bw_cex.summarize(
		    not_exprt(failed_exprs[i]));
		  property_map[it->first].result = summarizer_bw_cex.check();
		  if(property_map[it->first].result == 
		     property_checkert::FAIL)
		    break;
		}
		solver.new_context();
	      }
	    }
	  else
	    property_map[it->first].result = property_checkert::FAIL;
	}
    }
  
  _iterations++; //statistics
}
