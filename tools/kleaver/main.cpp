//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

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


#include "llvm/Support/Signals.h"
#include "../../lib/Core/TimingSolver.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/ADT/OwningPtr.h"
#include "llvm/Support/system_error.h"
#endif
#define EVENT_SIZE  ( sizeof (struct inotify_event) )
#define EVENT_BUF_LEN     ( 1024 * ( EVENT_SIZE + 16 ) )
using namespace llvm;
using namespace klee;
using namespace klee::expr;

namespace {
//    llvm::cl::opt<std::string>
//            InputFile(llvm::cl::desc("<input query log>"), llvm::cl::Positional,
//                      llvm::cl::init("-"));
    llvm::cl::opt<std::string>
            InputFile2(llvm::cl::desc("monitor file"), llvm::cl::Positional, llvm::cl::init("-"));

    enum ToolActions {
        PrintTokens,
        PrintAST,
        PrintSMTLIBv2,
        Evaluate
    };

    static llvm::cl::opt<ToolActions>
            ToolAction(llvm::cl::desc("Tool actions:"),
                       llvm::cl::init(Evaluate),
                       llvm::cl::values(
                               clEnumValN(PrintTokens, "print-tokens",
                                          "Print tokens from the input file."),
                               clEnumValN(PrintSMTLIBv2, "print-smtlib",
                                          "Print parsed input file as SMT-LIBv2 query."),
                               clEnumValN(PrintAST, "print-ast",
                                          "Print parsed AST nodes from the input file."),
                               clEnumValN(Evaluate, "evaluate",
                                          "Print parsed AST nodes from the input file.")KLEE_LLVM_CL_VAL_END));


    enum BuilderKinds {
        DefaultBuilder,
        ConstantFoldingBuilder,
        SimplifyingBuilder
    };

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


    llvm::cl::opt<std::string> directoryToWriteQueryLogs("query-log-dir", llvm::cl::desc(
            "The folder to write query logs to. Defaults is current working directory."),
                                                         llvm::cl::init("."));

    llvm::cl::opt<bool> ClearArrayAfterQuery(
            "clear-array-decls-after-query",
            llvm::cl::desc("We discard the previous array declarations after a query "
                                   "is performed. Default: false"),
            llvm::cl::init(false));
}


//std::string InputFile;
Solver *S;
Solver *coreSolver;
Parser *P;


void writeResult(std::vector<std::vector<unsigned char> > &result, QueryCommand *QC, const char *filename);

static std::string getQueryLogPath(const char filename[]) {
    //check directoryToWriteLogs exists
    struct stat s;
    if (!(stat(directoryToWriteQueryLogs.c_str(), &s) == 0 && S_ISDIR(s.st_mode))) {
        llvm::errs() << "Directory to log queries \""
                     << directoryToWriteQueryLogs << "\" does not exist!"
                     << "\n";
        exit(1);
    }

    //check permissions okay
    if (!((s.st_mode & S_IWUSR) && getuid() == s.st_uid) &&
        !((s.st_mode & S_IWGRP) && getgid() == s.st_gid) &&
        !(s.st_mode & S_IWOTH)
            ) {
        llvm::errs() << "Directory to log queries \""
                     << directoryToWriteQueryLogs << "\" is not writable!"
                     << "\n";
        exit(1);
    }

    std::string path = directoryToWriteQueryLogs;
    path += "/";
    path += filename;
    return path;
}

static std::string escapedString(const char *start, unsigned length) {
    std::string Str;
    llvm::raw_string_ostream s(Str);
    for (unsigned i = 0; i < length; ++i) {
        char c = start[i];
        if (isprint(c)) {
            s << c;
        } else if (c == '\n') {
            s << "\\n";
        } else {
            s << "\\x"
              << hexdigit(((unsigned char) c >> 4) & 0xF)
              << hexdigit((unsigned char) c & 0xF);
        }
    }
    return s.str();
}

static void PrintInputTokens(const MemoryBuffer *MB) {
    Lexer L(MB);
    Token T;
    do {
        L.Lex(T);
        llvm::outs() << "(Token \"" << T.getKindName() << "\" "
                     << "\"" << escapedString(T.start, T.length) << "\" "
                     << T.length << " " << T.line << " " << T.column << ")\n";
    } while (T.kind != Token::EndOfFile);
}

static bool PrintInputAST(const char *Filename,
                          const MemoryBuffer *MB,
                          ExprBuilder *Builder) {
    std::vector<Decl *> Decls;
    P = Parser::Create(Filename, MB, Builder, ClearArrayAfterQuery);
    P->SetMaxErrors(20);

    unsigned NumQueries = 0;
    while (Decl *D = P->ParseTopLevelDecl()) {
        if (!P->GetNumErrors()) {
            if (isa<QueryCommand>(D))
                llvm::outs() << "# Query " << ++NumQueries << "\n";

            D->dump();
        }
        Decls.push_back(D);
    }

    bool success = true;
    if (unsigned N = P->GetNumErrors()) {
        llvm::errs() << Filename << ": parse failure: " << N << " errors.\n";
        success = false;
    }

    for (std::vector<Decl *>::iterator it = Decls.begin(),
                 ie = Decls.end(); it != ie; ++it)
        delete *it;

    delete P;

    return success;
}

bool EvaluateInputAST(const char *Filename,
                             const MemoryBuffer *MB,
                             ExprBuilder *Builder) {
    std::vector<Decl *> Decls;
    P = Parser::Create(Filename, MB, Builder, ClearArrayAfterQuery);



    P->SetMaxErrors(20);
    while (Decl *D = P->ParseTopLevelDecl()) {
        Decls.push_back(D);
    }

    bool success = true;
    if (unsigned N = P->GetNumErrors()) {
        llvm::errs() << Filename << ": parse failure: " << N << " errors.\n";
        success = false;
    }

    if (!success)
        return false;


    if (CoreSolverToUse != DUMMY_SOLVER) {
        if (0 != MaxCoreSolverTime) {
            coreSolver->setCoreSolverTimeout(MaxCoreSolverTime);
        }
    }

    unsigned Index = 0;
    for (std::vector<Decl *>::iterator it = Decls.begin(),
                 ie = Decls.end(); it != ie; ++it) {
        Decl *D = *it;
        if (QueryCommand *QC = dyn_cast<QueryCommand>(D)) {
            assert("FIXME: Support counterexample query commands!");
            if (QC->Values.empty() && QC->Objects.empty()) {
                bool result;
                if (S->mustBeTrue(Query(ConstraintManager(QC->Constraints), QC->Query),
                                  result)) {
                    llvm::outs() << (result ? "VALID" : "INVALID");
                } else {
                    llvm::outs() << "FAIL (reason: "
                                 << SolverImpl::getOperationStatusString(S->impl->getOperationStatusCode())
                                 << ")";
                }
            } else if (!QC->Values.empty()) {
                assert(QC->Objects.empty() &&
                       "FIXME: Support counterexamples for values and objects!");
                assert(QC->Values.size() == 1 &&
                       "FIXME: Support counterexamples for multiple values!");
                assert(QC->Query->isFalse() &&
                       "FIXME: Support counterexamples with non-trivial query!");
                ref<ConstantExpr> result;
                if (S->getValue(Query(ConstraintManager(QC->Constraints),
                                      QC->Values[0]),
                                result)) {
                    llvm::outs() << "INVALID\n";
                    llvm::outs() << "\tExpr 0:\t" << result;
                } else {
                    llvm::outs() << "FAIL (reason: "
                                 << SolverImpl::getOperationStatusString(S->impl->getOperationStatusCode())
                                 << ")";
                }
            } else {
                std::vector<std::vector<unsigned char> > result;

                if (S->getInitialValues(Query(ConstraintManager(QC->Constraints), QC->Query),
                                        QC->Objects, result)) {
                    writeResult(result, QC, Filename);
//                    llvm::raw_ostream *out = &llvm::outs();
//                    ExprPPrinter::printConstraints(*out, ConstraintManager(QC->Constraints));
//                    ExprPPrinter::printQuery(*out, ConstraintManager(QC->Constraints), )
//                    std::cout << S->getConstraintLog(Query(ConstraintManager(QC->Constraints),
//                                              QC->Query)) << "\n";

//                    llvm::outs() << "INVALID\n";
//
//                    for (unsigned i = 0, e = result.size(); i != e; ++i) {
//                        llvm::outs() << "\tArray " << i << ":\t"
//                                     << QC->Objects[i]->name
//                                     << "[";
//                        for (unsigned j = 0; j != QC->Objects[i]->size; ++j) {
//                            llvm::outs() << (unsigned) result[i][j];
//                            if (j + 1 != QC->Objects[i]->size)
//                                llvm::outs() << ", ";
//                        }
//                        llvm::outs() << "]";
//                        if (i + 1 != e)
//                            llvm::outs() << "\n";
//                    }
                } else {
                    SolverImpl::SolverRunStatus retCode = S->impl->getOperationStatusCode();
                    if (SolverImpl::SOLVER_RUN_STATUS_TIMEOUT == retCode) {
                        llvm::outs() << " FAIL (reason: "
                                     << SolverImpl::getOperationStatusString(retCode)
                                     << ")";
                    } else {
                        llvm::outs() << "VALID (counterexample request ignored)";
                    }
                }
            }

            llvm::outs() << "\n";
            ++Index;

        }

    }

    for (std::vector<Decl *>::iterator it = Decls.begin(),
                 ie = Decls.end(); it != ie; ++it)
        delete *it;

    delete P;
//    delete Builder;
//  delete S;
//    S = 0;

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

    return success;
}

static bool printInputAsSMTLIBv2(const char *Filename,
                                 const MemoryBuffer *MB,
                                 ExprBuilder *Builder) {
    //Parse the input file
    std::vector<Decl *> Decls;
    P = Parser::Create(Filename, MB, Builder, ClearArrayAfterQuery);
    P->SetMaxErrors(20);
    while (Decl *D = P->ParseTopLevelDecl()) {
        Decls.push_back(D);
    }

    bool success = true;
    if (unsigned N = P->GetNumErrors()) {
        llvm::errs() << Filename << ": parse failure: "
                     << N << " errors.\n";
        success = false;
    }

    if (!success)
        return false;

    ExprSMTLIBPrinter printer;
    printer.setOutput(llvm::outs());

    unsigned int queryNumber = 0;
    //Loop over the declarations
    for (std::vector<Decl *>::iterator it = Decls.begin(), ie = Decls.end(); it != ie; ++it) {
        Decl *D = *it;
        if (QueryCommand *QC = dyn_cast<QueryCommand>(D)) {
            //print line break to separate from previous query
            if (queryNumber != 0) llvm::outs() << "\n";

            //Output header for this query as a SMT-LIBv2 comment
            llvm::outs() << ";SMTLIBv2 Query " << queryNumber << "\n";

            /* Can't pass ConstraintManager constructor directly
             * as argument to Query object. Like...
             * query(ConstraintManager(QC->Constraints),QC->Query);
             *
             * For some reason if constructed this way the first
             * constraint in the constraint set is set to NULL and
             * will later cause a NULL pointer dereference.
             */
            ConstraintManager constraintM(QC->Constraints);
            Query query(constraintM, QC->Query);
            printer.setQuery(query);

            if (!QC->Objects.empty())
                printer.setArrayValuesToGet(QC->Objects);

            printer.generateOutput();


            queryNumber++;
        }
    }

    //Clean up
    for (std::vector<Decl *>::iterator it = Decls.begin(),
                 ie = Decls.end(); it != ie; ++it)
        delete *it;
    delete P;

    return true;
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

void writeResult(std::vector<std::vector<unsigned char> > &result, QueryCommand *QC, const char *filename) {

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

void exitHandler() {
    std::cout << "delete S" << std::endl;
}

int main(int argc, char **argv) {
    bool success = true;

    llvm::sys::PrintStackTraceOnErrorSignal();
    llvm::cl::SetVersionPrinter(klee::printVersion);
    llvm::cl::ParseCommandLineOptions(argc, argv);



    std::ifstream in(InputFile2.c_str());

    std::string ErrorStr;


#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
    OwningPtr<MemoryBuffer> MB;
    error_code ec=MemoryBuffer::getFileOrSTDIN(InputFile.c_str(), MB);
    if (ec) {
      llvm::errs() << InputFile.c_str() << ": error: " << ec.message() << "\n";
      return 1;
    }
#else

    /* Watch File changes*/
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

    coreSolver = klee::createCoreSolver(CoreSolverToUse);
    S = constructSolverChain(coreSolver,
                             getQueryLogPath(ALL_QUERIES_SMT2_FILE_NAME),
                             getQueryLogPath(SOLVER_QUERIES_SMT2_FILE_NAME),
                             getQueryLogPath(ALL_QUERIES_KQUERY_FILE_NAME),
                             getQueryLogPath(SOLVER_QUERIES_KQUERY_FILE_NAME));

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


        auto MBResult = MemoryBuffer::getFile(InputFile.c_str());
        if (!MBResult) {
            llvm::errs() << InputFile.c_str() << ": error: " << MBResult.getError().message()
                         << "\n";
            return 1;
        }
        std::unique_ptr<MemoryBuffer> &MB = *MBResult;

//        std::cout << MB.get() << std::endl;
#endif

        ExprBuilder *Builder = 0;
        switch (BuilderKind) {
            case DefaultBuilder:
                Builder = createDefaultExprBuilder();
                break;
            case ConstantFoldingBuilder:
                Builder = createDefaultExprBuilder();
                Builder = createConstantFoldingExprBuilder(Builder);
                break;
            case SimplifyingBuilder:
                Builder = createDefaultExprBuilder();
                Builder = createConstantFoldingExprBuilder(Builder);
                Builder = createSimplifyingExprBuilder(Builder);
                break;
        }

        switch (ToolAction) {
            case PrintTokens:
                PrintInputTokens(MB.get());
                break;
            case PrintAST:
                success = PrintInputAST(InputFile == "-" ? "<stdin>" : InputFile.c_str(), MB.get(),
                                        Builder);
                break;
            case Evaluate:
                success = EvaluateInputAST(InputFile.c_str(),
                                           MB.get(), Builder);
                break;
            case PrintSMTLIBv2:
                success = printInputAsSMTLIBv2(InputFile == "-" ? "<stdin>" : InputFile.c_str(), MB.get(), Builder);
                break;
            default:
                llvm::errs() << argv[0] << ": error: Unknown program action!\n";
        }

        delete Builder;
        InputFile.clear();
        llvm::llvm_shutdown();
    }
    in.close();
    llvm::llvm_shutdown();
//    delete S;
    return success ? 0 : 1;
}
