include ../config.inc

SRC = summarizer_base.cpp  \
      summarizer_fw.cpp summarizer_bw.cpp \
      summarizer_bw_cex.cpp summarizer_bw_cex_complete.cpp \
      summarizer_bw_cex_concrete.cpp  \
      summarizer_bw_cex_wp.cpp  \
      summarizer_bw_cex_ai.cpp summarizer_bw_cex_all.cpp \
      summarizer_fw_contexts.cpp \
      summarizer_main.cpp summarizer_parse_options.cpp \
      show.cpp summary_checker_base.cpp \
      summary_checker_ai.cpp summary_checker_bmc.cpp \
      summary_checker_kind.cpp \
      cover_goals_ext.cpp \
      summary_db.cpp summary.cpp ssa_db.cpp \
      array_abstraction.cpp preprocessing_util.cpp \
      instrument_goto.cpp function_signature.cpp

OBJ+= $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/json/json$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \


DELTA_OBJ+=\
      $(CBMC)/src/goto-instrument/unwind$(OBJEXT) \
      ../ssa/ssa_slicer$(OBJEXT) \
      ../ssa/malloc_ssa$(OBJEXT) \
      ../ssa/ssa_domain$(OBJEXT) \
      ../ssa/assignments$(OBJEXT) \
      ../ssa/guard_map$(OBJEXT) \
      ../ssa/ssa_object$(OBJEXT) \
      ../ssa/address_canonizer$(OBJEXT) \
      ../ssa/ssa_dereference$(OBJEXT) \
      ../ssa/simplify_ssa$(OBJEXT) \
      ../ssa/ssa_build_goto_trace$(OBJEXT) \
      ../ssa/split_loopheads$(OBJEXT)\
      ../ssa/ssa_inliner$(OBJEXT)\
      ../ssa/ssa_unwinder$(OBJEXT)\
      ../ssa/ssa_value_set$(OBJEXT) \
      ../ssa/const_propagator$(OBJEXT) \
      ../ssa/replace_symbol_ext$(OBJEXT) \
      ../ssa/ssa_const_propagator$(OBJEXT) \
      ../ssa/ssa_dependency_graph$(OBJEXT) \
      ../functions/summary$(OBJEXT) \
      ../functions/get_function$(OBJEXT) \
      ../functions/path_util$(OBJEXT) \
      ../functions/index$(OBJEXT) \
      ../functions/index$(OBJEXT) \
      ../domains/fixed_point$(OBJEXT) \
      ../domains/ssa_fixed_point$(OBJEXT) \
      ../domains/tpolyhedra_domain$(OBJEXT) \
      ../domains/predabs_domain$(OBJEXT) \
      ../domains/equality_domain$(OBJEXT) \
      ../domains/domain$(OBJEXT) \
      ../domains/util$(OBJEXT) \
      ../domains/incremental_solver$(OBJEXT) \
      ../domains/strategy_solver_base$(OBJEXT) \
      ../domains/strategy_solver_predabs$(OBJEXT) \
      ../domains/strategy_solver_equality$(OBJEXT) \
      ../domains/strategy_solver_enumeration$(OBJEXT) \
      ../domains/strategy_solver_binsearch$(OBJEXT) \
      ../domains/strategy_solver_binsearch2$(OBJEXT) \
      ../domains/strategy_solver_binsearch3$(OBJEXT) \
      ../domains/template_generator_base$(OBJEXT) \
      ../domains/template_generator_summary$(OBJEXT) \
      ../domains/template_generator_callingcontext$(OBJEXT) \
      ../domains/ssa_analyzer$(OBJEXT) \
      ../domains/disjunctive_analyzer$(OBJEXT) \
      ../domains/predicate$(OBJEXT)
#      ../domains/solver_enumeration$(OBJEXT) 


OBJ+=$(DELTA_OBJ)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS+= $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src
# \
#  -I $(CUDD)/cudd -I $(CUDD)/obj -I $(CUDD)/mtr -I $(CUDD)/epd

LIBS =
#LIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/mtr/libmtr.a \
#       $(CUDD)/st/libst.a $(CUDD)/epd/libepd.a $(CUDD)/util/libutil.a

#CP_CXXFLAGS +=-g -DSHOW_CALLING_CONTEXTS

# $(CUDD)/obj/libobj.a 

CLEANFILES = summarizer$(EXEEXT) $(DELTA_OBJ)

all: summarizer$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/java/Makefile),)
  OBJ += $(CBMC)/src/java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

###############################################################################

summarizer$(EXEEXT): $(OBJ)
	$(LINKBIN)

