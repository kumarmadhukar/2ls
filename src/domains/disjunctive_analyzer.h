/*******************************************************************\

Module: Data Flow Analysis

Author: Peter Schrammel, Kumar Madhukar

\*******************************************************************/

#ifndef DELTACHECK_DISJUNCTIVE_ANALYZER_H
#define DELTACHECK_DISJUNCTIVE_ANALYZER_H

class disjunctive_analyzert : public messaget
{
 public:
  explicit disjunctive_analyzert()
    :
  solver_instances(0),
    solver_calls(0)
      {
      }  
  
  ~disjunctive_analyzert() 
    {
    }

  void eliminate_implication(exprt &formula);
  void push_negation_to_atoms(exprt &formula);
  void convert_to_dnf(exprt &formula);
  void convert_to_dnf_rec(exprt &formula);
  
  bool operator()(incremental_solvert &solver,
		  local_SSAt &SSA,
		  const exprt &side_conditions,
		  template_generator_baset &template_generator,
		  const exprt &disjunctive_conditions,
		  exprt &result_expr,
		  const domaint::var_sett &vars
		  );

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }
  
protected:
  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
};


#endif
 
