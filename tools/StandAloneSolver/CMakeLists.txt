#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(standalone
  main.cpp
       SharedQueue.h)

set(KLEE_LIBS
  kleaverSolver
)

target_link_libraries(standalone ${KLEE_LIBS})

install(TARGETS standalone RUNTIME DESTINATION bin)
