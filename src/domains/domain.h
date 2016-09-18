#ifndef CPROVER_DOMAIN_H
#define CPROVER_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <util/i2string.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>
#include <util/namespace.h>

class domaint
{
public:
  domaint(unsigned _domain_number, 
	 replace_mapt &_renaming_map, 
	 const namespacet &_ns) : 
    domain_number(_domain_number), 
    renaming_map(_renaming_map),
    ns(_ns)
  {}
  virtual ~domaint() {}

  typedef exprt vart;
  typedef std::vector<vart> var_listt;
  typedef std::set<vart> var_sett;

  typedef enum {LOOP, IN, OUT, OUTL} kindt;

  typedef exprt guardt; 

  typedef struct {
    guardt pre_guard;
    guardt post_guard;
    vart var;
    exprt aux_expr; //some auxiliary per-variable constraint
    kindt kind;
  } var_spect;

  typedef std::vector<var_spect> var_specst; 

  class valuet {
   public:
    virtual ~valuet() {}
  };

  virtual void initialize(valuet &value) { assert(false); }

  //returns true as long as further refinements are possible
  virtual void reset_refinements() { }
  virtual bool refine() { return false; }

  virtual void join(valuet &value1, const valuet &value2) { assert(false); }

  virtual void output_value(std::ostream &out, const valuet &value, 
    const namespacet &ns) const { assert(false); }
  virtual void output_domain(std::ostream &out, 
    const namespacet &ns) const { assert(false); }

  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result) 
    { assert(false); } //(not useful to make value const (e.g. union-find))

  virtual bool is_spec_empty() const { assert(false); }
  
  static kindt merge_kinds(kindt k1, kindt k2);

  static void output_var_specs(std::ostream &out, const var_specst &var_specs,
			       const namespacet &ns);

 protected:
  unsigned domain_number; //serves as id for variables names
  replace_mapt &renaming_map;
  const namespacet &ns;
  
  inline void rename(exprt &expr) 
  { 
    replace_expr(renaming_map, expr); 
  }
  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }

};

#endif
