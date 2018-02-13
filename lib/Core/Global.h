//
// Created by jiakuan on 12/19/17.
//
#include "klee/ExecutionState.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/util/ArrayCache.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/Twine.h"
#include <vector>
#include <string>
#include <set>
#include <queue>

#ifndef KLEE_GLOBAL_H
#define KLEE_GLOBAL_H

extern std::queue<std::pair<unsigned int, int>> id_guide;
extern std::queue<std::pair<int, int>> switch_guide;
extern std::queue<std::pair<int, int>> malloc_guide;
extern std::queue<std::pair<int, int>> memop_guide;
extern klee::KInstruction* current_ki;
extern klee::KInstruction* prev_ki;
extern bool concrete_run;
extern int pop_count;
extern char* post_url;
extern int post_port;
extern std::queue<klee::InstructionInfo> instruction_info;
extern bool async_mode;
#endif //KLEE_GLOBAL_H
