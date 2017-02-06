
#include <iostream>
#include <util/find_symbols.h>
#include <langapi/language_util.h>

#include "ssa_dependency_graph.h"

void ssa_dependency_grapht::output(std::ostream &out) const
{
  for(unsigned index = 0; index < depnodes_map.size(); index++)
    {
      out << "Node#" << index << "; info: "  << from_expr(ns, "", depnodes_map[index].node_info) << "\n";
      out << "Node#" << index << "; -> Used Symbols: "; 
      for(find_symbols_sett::const_iterator u_it=depnodes_map[index].used_symbols.begin();
	  u_it!=depnodes_map[index].used_symbols.end(); u_it++){
	out << *u_it << " ";
      }
      out << "\n";

      out << "Node#" << index << "; -> Modified Symbols: "; 
      for(find_symbols_sett::const_iterator m_it=depnodes_map[index].modified_symbols.begin();
	  m_it!=depnodes_map[index].modified_symbols.end(); m_it++){
	out << *m_it << " ";
      }
      out << "\n";

      out << "Successors: ";
      for(unsigned i = 0; i < depnodes_map[index].successors.size(); i++){
	out << depnodes_map[index].successors[i] << " ";
      }
      out << "\n";

      out << "Predecessors:\n";
      for(ssa_dependency_grapht::annotated_predecessorst::const_iterator p_it = depnodes_map[index].predecessors.begin();
	  p_it != depnodes_map[index].predecessors.end(); p_it++){
	annotated_predecessort pred = *p_it;
	int pred_index = pred.predecessor_node_index;
	find_symbols_sett pred_annotation = pred.annotation;
	out << "    " << "Predecessor Node#" << pred_index << "; Annotation: ";
	for(find_symbols_sett::const_iterator s_it=pred_annotation.begin();
	    s_it!=pred_annotation.end(); s_it++){ out << *s_it << " "; }
	out << "\n"; } out << "\n";
    }
  out << "\n\n";
}

void ssa_dependency_grapht::create(const local_SSAt &SSA, ssa_inlinert &ssa_inliner, bool entry)
{
  depnodet sink_node;
  sink_node.is_assertion = false;
  sink_node.is_function_call = false;
  sink_node.is_loop = false;
 
  // globals_out is the used_symbol of the sink_node
  for(local_SSAt::var_sett::const_iterator g_it = SSA.globals_out.begin();
      g_it != SSA.globals_out.end(); g_it++){
    irep_idt id = (*g_it).get(ID_identifier);
    sink_node.used_symbols.insert(id);
  }
  
  exprt function_guard = SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  //std::cout << "function guard: " << from_expr(ns, "", function_guard) << "\n";
  
  irep_idt id = function_guard.get(ID_identifier);
  //std::cout << "guard identifier: " << id << "\n";
  sink_node.used_symbols.insert(id);
  
  depnodes_map.push_back(sink_node);

  // collect all the symbols to iterate over it
  find_symbols_sett all_ssa_symbols;

  bool first_node = true;
  bool ignore_equality = false;
  bool ignore_equality_done = false;
  
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    const local_SSAt::nodet &node=*n_it;

    // check whether this node is enabled
    if(!node.enabling_expr.is_true())
    {
      bool enabled=true;
      const irep_idt &enable=to_symbol_expr(node.enabling_expr).get_identifier();
      for(size_t i=0; i<SSA.enabling_exprs.size(); ++i)
      {
        if(SSA.enabling_exprs[i].id()==ID_not)
        {
          if(to_symbol_expr(SSA.enabling_exprs[i].op0()).get_identifier()==enable)
          {
            enabled=false;
            break;
          }
        }
      }
      if(!enabled)
        continue;
    }

    // collecting symbols from equalities and populating dependency graph nodes
    for(local_SSAt::nodet::equalitiest::const_iterator e_it=node.equalities.begin();
	e_it!=node.equalities.end(); e_it++)
      {

	find_symbols(*e_it,all_ssa_symbols);
	
	depnodet temp_node;
	temp_node.is_assertion = false;
	temp_node.is_function_call = false;
  temp_node.is_loop = false;
	temp_node.node_info = *e_it;
	temp_node.location = n_it->location;

  //loop-head select
  //TODO: this is an ugly hack (this can be changed as soon as unwindable_local_SSA provides smooth renaming with odometers)
  //if(n_it->loophead!=SSA.nodes.end())
  if(e_it->op1().id()==ID_if &&
     e_it->op1().op0().id()==ID_symbol)
  {
    std::string var_string = id2string(e_it->op1().op0().get(ID_identifier));
	  if(((var_string.substr(0,14)) == "ssa::$guard#ls"))
    {
      temp_node.is_loop = true;
/*    symbol_exprt lsguard = SSA.name(SSA.guard_symbol(),
				    local_SSAt::LOOP_SELECT, n_it->location);
            ssa_local_unwinder.unwinder_rename(lsguard,*n_it,true);*/
      temp_node.guard = not_exprt(e_it->op1().op0());
    }
  }
	//temp_node.trivial_guard = true;
	
	equal_exprt e = to_equal_expr(*e_it);
	exprt &lhs = e.lhs(); exprt &rhs = e.rhs();

	find_symbols(rhs,temp_node.used_symbols);
	find_symbols(lhs,temp_node.modified_symbols);

	if(!ignore_equality_done){
	  std::string var_string = id2string(to_symbol_expr(lhs).get_identifier());
	  if(((var_string.substr(0,11)) == "ssa::$guard") && (rhs.is_true())){
	    ignore_equality = true;
	    ignore_equality_done = true;
	  }
	}
	
	if(first_node && ignore_equality){
	  if(entry){
	    depnodes_map.push_back(temp_node);
	    //std::cout << "created equality node, with info: " << from_expr(ns, "", *e_it) << "\n";
	  }
	  ignore_equality = false;
	}
	else{
	  depnodes_map.push_back(temp_node);
	  //std::cout << "created equality node, with info: " << from_expr(ns, "", *e_it) << "\n";
	}
	
      }

    // collecting symbols from constraints and populating dependency graph nodes
    for(local_SSAt::nodet::constraintst::const_iterator c_it=node.constraints.begin();
	c_it!=node.constraints.end(); c_it++)
      {
	find_symbols(*c_it,all_ssa_symbols);
	
	depnodet temp_node;
	temp_node.is_assertion = false;
	temp_node.is_function_call = false;
  temp_node.is_loop = false;
	temp_node.node_info = *c_it;
	temp_node.location = n_it->location;
	find_symbols(*c_it,temp_node.used_symbols);
	find_symbols(*c_it,temp_node.modified_symbols);
	depnodes_map.push_back(temp_node);
	//std::cout << "created constraint node, with info: " << from_expr(ns, "", *c_it) << "\n";
      }
    
    // collecting symbols from assertionst and populating dependency graph nodes
    for(local_SSAt::nodet::assertionst::const_iterator a_it=node.assertions.begin();
	a_it!=node.assertions.end(); a_it++)
      {
	find_symbols(*a_it,all_ssa_symbols);

	depnodet temp_node;
	temp_node.is_assertion = true;
	temp_node.is_function_call = false;
  temp_node.is_loop = false;
	temp_node.node_info = *a_it;
	temp_node.location = n_it->location;
	find_symbols(*a_it,temp_node.used_symbols);
	depnodes_map.push_back(temp_node);
	//std::cout << "created assertion node, with info: " << from_expr(ns, "", *a_it) << "\n";
      }

    /*
    // collecting symbols from assumptionst and populating dependency graph nodes
    for(local_SSAt::nodet::assumptionst::const_iterator a_it=node.assumptions.begin();
	a_it!=node.assumptions.end(); a_it++)
      {
	find_symbols(*a_it,all_ssa_symbols);
	
	depnodet temp_node;
	temp_node.is_assertion = false;
	temp_node.is_function_call = false;
	temp_node.node_info = *a_it;
	find_symbols(*a_it,temp_node.used_symbols);
	find_symbols(*a_it,temp_node.modified_symbols);
	depnodes_map.push_back(temp_node);
	//std::cout << "created assumption node, with info: " << from_expr(ns, "", *a_it) << "\n";
      }
    */

    // collecting symbols from function_callst and populating dependency graph nodes
    for(local_SSAt::nodet::function_callst::const_iterator f_it=node.function_calls.begin();
	f_it!=node.function_calls.end(); f_it++)
      {
	//find_symbols(*f_it,all_ssa_symbols);

	irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
	if(ssa_db.exists(fname))
	  {
	    const local_SSAt &fSSA = ssa_db.get(fname);
	    
	    /******************************************************************/
	    /******* additional nodes needed to fix the dependency tree *******/

	    exprt guard_binding;
	    exprt::operandst bindings_in, bindings_out;
	    int counter = ssa_inliner.get_rename_counter();

	    /**/
	    ssa_inliner.get_guard_binding(SSA,fSSA,n_it,guard_binding,counter);
	    //std::cout << "guard binding: " << from_expr(ns, "", guard_binding) << "\n";
	    /*
	    {
	      depnodet temp_node;
	      temp_node.is_assertion = false;
	      temp_node.is_function_call = false;
	      temp_node.node_info = guard_binding;
	      
	      equal_exprt e = to_equal_expr(guard_binding);
	      exprt &lhs = e.lhs(); exprt &rhs = e.rhs();
	      
	      find_symbols(rhs,temp_node.used_symbols);
	      find_symbols(lhs,temp_node.modified_symbols);
	      depnodes_map.push_back(temp_node);
	      //std::cout << "created guard binding node, with info: " << from_expr(ns, "", guard_binding) << "\n";
	    }
	    */
	    /**/

	    ssa_inliner.get_bindings(SSA,fSSA,n_it,f_it,bindings_in,bindings_out,counter);
	    
	    for(exprt::operandst::const_iterator b_it=bindings_in.begin();
		b_it!=bindings_in.end(); b_it++){
	      
	      //std::cout << "binding: " << from_expr(ns, "", *b_it) << "\n";

	      depnodet temp_node;
	      temp_node.is_assertion = false;
	      temp_node.is_function_call = false;
        temp_node.is_loop = false;
	      temp_node.node_info = *b_it;
  	      temp_node.location = n_it->location;
	      
	      equal_exprt e = to_equal_expr(*b_it);
	      exprt &lhs = e.lhs(); exprt &rhs = e.rhs();
	      
	      find_symbols(rhs,temp_node.used_symbols);
	      find_symbols(lhs,temp_node.modified_symbols);
	      depnodes_map.push_back(temp_node);
	      //std::cout << "created binding in node, with info: " << from_expr(ns, "", *b_it) << "\n";
	    }

	    for(exprt::operandst::const_iterator b_it=bindings_out.begin();
		b_it!=bindings_out.end(); b_it++){

	      //std::cout << "binding: " << from_expr(ns, "", *b_it) << "\n";
	      
	      depnodet temp_node;
	      temp_node.is_assertion = false;
	      temp_node.is_function_call = false;
        temp_node.is_loop = false;
	      temp_node.node_info = *b_it;
	      temp_node.location = n_it->location;

	      equal_exprt e = to_equal_expr(*b_it);
	      exprt &lhs = e.lhs(); exprt &rhs = e.rhs();
	      
	      find_symbols(rhs,temp_node.used_symbols);
	      find_symbols(lhs,temp_node.modified_symbols);
	      depnodes_map.push_back(temp_node);
	      //std::cout << "created binding out node, with info: " << from_expr(ns, "", *b_it) << "\n";
	    }

	    /******************************************************************/

	    depnodet temp_node;
	    temp_node.guard = guard_binding;
	    temp_node.is_assertion = false;
	    temp_node.is_function_call = true;
      temp_node.is_loop = false;
	    temp_node.node_info = *f_it;
	    temp_node.rename_counter = counter;
  	    temp_node.location = n_it->location;

	    find_symbols(guard_binding,temp_node.used_symbols);

	    for(local_SSAt::var_listt::const_iterator p_it = fSSA.params.begin();
		p_it != fSSA.params.end(); p_it++){
	      irep_idt id = (*p_it).get(ID_identifier);
	      ssa_inliner.rename(id, counter);
	      all_ssa_symbols.insert(id);
	      temp_node.used_symbols.insert(id);
	    }

	    for(local_SSAt::var_sett::const_iterator g_it = fSSA.globals_in.begin();
		g_it != fSSA.globals_in.end(); g_it++){
	      irep_idt id = (*g_it).get(ID_identifier);
	      ssa_inliner.rename(id, counter);
	      all_ssa_symbols.insert(id);
	      temp_node.used_symbols.insert(id);
	    }

	    for(local_SSAt::var_sett::const_iterator g_it = fSSA.globals_out.begin();
		g_it != fSSA.globals_out.end(); g_it++){
	      irep_idt id = (*g_it).get(ID_identifier);
	      ssa_inliner.rename(id, counter);
	      all_ssa_symbols.insert(id);
	      temp_node.modified_symbols.insert(id);
	    }
	    
	    depnodes_map.push_back(temp_node);
	    //std::cout << "created function node, with info: " << from_expr(ns, "", *f_it) << "\n";
	  }
      }
  }
  first_node = false;
  
  depnodet source_node;
  source_node.is_assertion = false;
  source_node.is_function_call = false;
  source_node.is_loop = false;
  
  // params and globals_in are the modified_symbols at source_node
  
  for(local_SSAt::var_listt::const_iterator p_it = SSA.params.begin();
      p_it != SSA.params.end(); p_it++){
    irep_idt id = (*p_it).get(ID_identifier);
    source_node.modified_symbols.insert(id);
  }
  
  for(local_SSAt::var_sett::const_iterator g_it = SSA.globals_in.begin();
      g_it != SSA.globals_in.end(); g_it++){
    irep_idt id = (*g_it).get(ID_identifier);
    source_node.modified_symbols.insert(id);
  }
  
  depnodes_map.push_back(source_node); // source_node
  //std::cout << "created source node, without any info" << "\n";
  
  top_node_index = depnodes_map.size() - 1;
  
  for(find_symbols_sett::const_iterator
	s_it=all_ssa_symbols.begin();  s_it!=all_ssa_symbols.end(); s_it++){

    for(unsigned m_index = 0; m_index < depnodes_map.size(); m_index++){
      if(depnodes_map[m_index].modified_symbols.find(*s_it) != depnodes_map[m_index].modified_symbols.end()){
	
	for(unsigned u_index = 0; u_index < depnodes_map.size(); u_index++){
	  
	  if(m_index != u_index){
	    if(depnodes_map[u_index].used_symbols.find(*s_it) != depnodes_map[u_index].used_symbols.end()){
	      annotated_predecessort temp_pred;
	      temp_pred.predecessor_node_index = m_index;
	      temp_pred.annotation.insert(*s_it);
	      depnodes_map[u_index].predecessors.push_back(temp_pred);
	      depnodes_map[m_index].successors.push_back(u_index);
	    }
	  }
	}
      }
    }
  }

  if(depnodes_map.size() == 2){

    //sink_node's successor is the source_node
    annotated_predecessort def_pred; // successors of the default predecessors
    def_pred.predecessor_node_index = top_node_index;
    def_pred.annotation = depnodes_map[0].used_symbols;
    depnodes_map[0].predecessors.push_back(def_pred);
    
    //source_node's successor is the sink_node
    depnodes_map[top_node_index].successors.push_back(0);
    
  }
  else{
    for(unsigned index = 1; index < depnodes_map.size() - 1; index++)
      {
      	// if node does not have a predecessor
	if(depnodes_map[index].predecessors.empty()){
	  //its predecessor is the source_node
	  annotated_predecessort def_pred; // successors of the default predecessors
	  def_pred.predecessor_node_index = top_node_index;
	  def_pred.annotation = depnodes_map[index].used_symbols;
	  depnodes_map[index].predecessors.push_back(def_pred);
	  
	  //source_node's successor is this node
	  depnodes_map[top_node_index].successors.push_back(index);
	}
	
	// if node does not have a successor
	if(depnodes_map[index].successors.empty()){
	  //its successor is the sink_node
	  depnodes_map[index].successors.push_back(0);
	  
	  //sink_node's predecessor is that node
	  annotated_predecessort pred_def; // predecessors of the default successor
	  pred_def.predecessor_node_index = index;
	  pred_def.annotation = depnodes_map[index].modified_symbols;
	  depnodes_map[0].predecessors.push_back(pred_def);
	}
      }
  }
  
}
