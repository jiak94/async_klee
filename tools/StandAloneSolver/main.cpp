#include "expr/Lexer.h"
#include "expr/Parser.h"

#include "klee/Config/Version.h"
#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/ExprBuilder.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/Statistics.h"
#include "klee/CommandLine.h"
#include "klee/Common.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprVisitor.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/Internal/Support/PrintVersion.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <sys/stat.h>
#include <unistd.h>
#include <sys/inotify.h>
#include <iostream>
#include <fstream>
#include <csignal>
#include <thread>
#include <mutex>
#include <condition_variable>

#include "llvm/Support/Signals.h"
#include "../../lib/Core/TimingSolver.h"
#include "SharedQueue.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/ADT/OwningPtr.h"
#include "llvm/Support/system_error.h"
#endif
#define EVENT_SIZE  ( sizeof (struct inotify_event) )
#define EVENT_BUF_LEN     ( 1024 * ( EVENT_SIZE + 16 ) )

//
// Created by jiakuan on 3/13/18.
//
using namespace llvm;
using namespace klee;
using namespace klee::expr;

enum BuilderKinds {
    DefaultBuilder,
    ConstantFoldingBuilder,
    SimplifyingBuilder
};

llvm::cl::opt<std::string>
        InputFile2(llvm::cl::desc("monitor file"), llvm::cl::Positional, llvm::cl::init("-"));

static llvm::cl::opt<BuilderKinds>
        BuilderKind("builder",
                    llvm::cl::desc("Expression builder:"),
                    llvm::cl::init(DefaultBuilder),
                    llvm::cl::values(
                            clEnumValN(DefaultBuilder, "default",
                                       "Default expression construction."),
                            clEnumValN(ConstantFoldingBuilder, "constant-folding",
                                       "Fold constant expressions."),
                            clEnumValN(SimplifyingBuilder, "simplify",
                                       "Fold constants and simplify expressions.")KLEE_LLVM_CL_VAL_END));


class Solution {
private:
    Solver *solver;
    Solver *coreSolver;
    ExprBuilder *builder;
    Parser *parser = NULL;
    BuilderKinds kinds;
    void writeResult(std::vector<std::vector<unsigned char> > &result, QueryCommand *QC, const char *filename);

public:
    Solution(BuilderKinds kind);
    bool parse(std::string Filename, MemoryBuffer *MB, std::vector<Decl *> &decls);
    void computeInitialValue(std::vector<Decl *> decls, std::string Filename);
};

Solution::Solution(BuilderKinds kind) {
    kinds = kind;
    coreSolver = klee::createCoreSolver(CoreSolverToUse);
    solver = constructSolverChain(coreSolver, "", "", "", "");
//    parser = Parser::Create(NULL, NULL, NULL, false);
    switch (kinds) {
        case DefaultBuilder:
            builder = createDefaultExprBuilder();
            break;
        case ConstantFoldingBuilder:
            builder = createDefaultExprBuilder();
            builder = createConstantFoldingExprBuilder(builder);
            break;
        case SimplifyingBuilder:
            builder = createDefaultExprBuilder();
            builder = createConstantFoldingExprBuilder(builder);
            builder = createSimplifyingExprBuilder(builder);
            break;
    }
}

bool Solution::parse(std::string Filename, MemoryBuffer *MB, std::vector<Decl *> &decls) {
    if (parser == NULL) {
        parser = Parser::Create(Filename, MB, builder, false);
    }
    else {
        parser->updateParserImpl(Filename, MB, builder);
    }
//    parser = Parser::Create(Filename, MB, builder, false);
//    parser->update(Filename, MB, builder);
//    std::vector<Decl *> Decls;

    parser->SetMaxErrors(20);
    while (Decl *D = parser->ParseTopLevelDecl()) {
        decls.push_back(D);
    }

    return true;
}


void Solution::computeInitialValue(std::vector<Decl *> decls, std::string Filename) {
    for (std::vector<Decl *>::iterator it = decls.begin(),
                 ie = decls.end(); it != ie; ++it) {
        Decl *D = *it;

        if (QueryCommand *QC = dyn_cast<QueryCommand>(D)) {
//            std::cout << solver->getConstraintLog(Query(ConstraintManager(QC->Constraints), QC->Query)) << std::endl;
            std::vector<std::vector<unsigned char> > result;
            if (solver->getInitialValues(Query(ConstraintManager(QC->Constraints), QC->Query),
                                         QC->Objects, result)) {
                this->writeResult(result, QC, Filename.c_str());
            }
        }
    }
            if (uint64_t queries = *theStatisticManager->getStatisticByName("Queries")) {
            llvm::outs()
                    << "--\n"
                    << "total queries = " << queries << "\n"
                    << "total queries constructs = "
                    << *theStatisticManager->getStatisticByName("QueriesConstructs") << "\n"
                    << "valid queries = "
                    << *theStatisticManager->getStatisticByName("QueriesValid") << "\n"
                    << "invalid queries = "
                    << *theStatisticManager->getStatisticByName("QueriesInvalid") << "\n"
                    << "query cex = "
                    << *theStatisticManager->getStatisticByName("QueriesCEX") << "\n"
                    << "query cex cache hits = "
                    << *theStatisticManager->getStatisticByName("QueryCexCacheHits") << "\n";
        }
        llvm::outs() << "\n";
}

void Solution::writeResult(std::vector<std::vector<unsigned char> > &result, QueryCommand *QC, const char *filename) {

    for (unsigned i = 0, e = result.size(); i != e; ++i) {
        std::string outfile = std::string(filename) + "_" + QC->Objects[i]->name + "_replay";
        std::ofstream out;
        out.open(outfile, std::ios::out);
        for (unsigned j = 0; j != QC->Objects[i]->size; ++j) {
            out << (char)result[i][j];
        }
        out.close();
    }
}


std::string getFilename(std::ifstream &in) {
    std::string res;
    std::string lastLine;
    in.clear();
    in.seekg(0);
    if (in.is_open()) {
        while (getline(in, lastLine)){
            res = lastLine;
        }
    }
    return res;
}

void monitor(SharedQueue &sharedqueue) {
    int fdnotify = -1;
    fdnotify = inotify_init();

    if (fdnotify < 0) {
        perror("inofity_init failed");
        exit(1);
    }

    int wd = inotify_add_watch(fdnotify, InputFile2.getValue().c_str(), IN_MODIFY);
    if (wd < 0) {
        perror("inotify_add_watch failed");
        exit(1);
    }
    std::ifstream in(InputFile2.c_str());
    while (1) {
        int len, i = 0;
        std::string InputFile;
        char buffer[EVENT_BUF_LEN];
        len = read(fdnotify, buffer, EVENT_SIZE);
        if (len < 0) {
            perror("read");
        }
        while ( i < len ) {
            struct inotify_event *event = ( struct inotify_event * ) &buffer[ i ];
            if( event->mask & IN_MODIFY) {
                InputFile = getFilename(in);
                std::cout << InputFile << std::endl;
            }
            i += EVENT_SIZE + sizeof(buffer);
        }

        sharedqueue.push_back(InputFile);
    }
}
void solve(Solution* &solution, SharedQueue &sharedqueue) {
    while (1) {
        while (!sharedqueue.empty()) {
            std::string InputFile = sharedqueue.front();
            sharedqueue.pop_front();

            auto MBResult = MemoryBuffer::getFile(InputFile.c_str());
            if (!MBResult) {
                llvm::errs() << InputFile.c_str() << ": error: " << MBResult.getError().message()
                             << "\n";
                exit(1);
            }
            std::unique_ptr<MemoryBuffer> &MB = *MBResult;

            std::vector<Decl *> decls;
            solution->parse(InputFile, MB.get(), decls);
            solution->computeInitialValue(decls, InputFile);
            std::cout << "start sleep" <<std::endl;
            usleep(3000000);
            std::cout << "end sleep" << std::endl;
            InputFile.clear();
        }
    }
}

int main(int argc, char **argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv);
    Solution *solution = new Solution(BuilderKind.getValue());
    SharedQueue queue;

    std::thread monitor_thread(monitor, std::ref(queue));
    solve(solution, queue);
}
