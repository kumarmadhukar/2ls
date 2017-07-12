include ../config.inc
CBMC ?= ../..

SRC = ssa_slicer.cpp local_ssa.cpp ssa_domain.cpp translate_union_member.cpp malloc_ssa.cpp \
      guard_map.cpp ssa_object.cpp assignments.cpp ssa_dereference.cpp \
      ssa_value_set.cpp address_canonizer.cpp simplify_ssa.cpp \
      ssa_build_goto_trace.cpp ssa_inliner.cpp ssa_unwinder.cpp \
      split_loopheads.cpp const_propagator.cpp ssa_const_propagator.cpp \
      replace_symbol_ext.cpp ssa_dependency_graph.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

