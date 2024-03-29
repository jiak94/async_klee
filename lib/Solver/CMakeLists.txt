#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
klee_add_component(kleaverSolver
  AssignmentValidatingSolver.cpp
  CachingSolver.cpp
  CexCachingSolver.cpp
  ConstantDivision.cpp
  CoreSolver.cpp
  DummySolver.cpp
  FastCexSolver.cpp
  IncompleteSolver.cpp
  IndependentSolver.cpp
  MetaSMTSolver.cpp
  KQueryLoggingSolver.cpp
  QueryLoggingSolver.cpp
  SMTLIBLoggingSolver.cpp
  Solver.cpp
  SolverImpl.cpp
  SolverStats.cpp
  STPBuilder.cpp
  STPSolver.cpp
  ValidatingSolver.cpp
  Z3Builder.cpp
  Z3Solver.cpp
)

set(LLVM_COMPONENTS
  support
)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -lcurl")
klee_get_llvm_libs(LLVM_LIBS ${LLVM_COMPONENTS})
target_link_libraries(kleaverSolver PUBLIC ${LLVM_LIBS} curl)

target_link_libraries(kleaverSolver PRIVATE
  kleeBasic
  kleaverExpr
  kleeSupport
  ${KLEE_SOLVER_LIBRARIES})

