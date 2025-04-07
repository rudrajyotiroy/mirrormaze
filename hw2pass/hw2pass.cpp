//===-- Updated LLVMSymmetricPass with Control Flow Analysis -----------===//
#include <iostream>
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Passes/PassPlugin.h"

enum ImportanceLevel {
    NONE = 0,  // No messages are logged.
    HIGH = 1,  // Only high-importance messages.
    MED  = 2,  // Medium-importance messages.
    LOW  = 3,  // Low-importance messages.
    ALL  = 4   // All messages are logged.
};

// Change here
#define VERBOSE ALL 

#define PRINT(x, v)                           \
  do {                                        \
    if (VERBOSE > (v)) {                      \
      errs() << "Line: " << __LINE__    \
             << ", Message: " << (x) << "\n";  \
    }                                         \
  } while(0)


using namespace llvm;
using namespace std;

namespace {

struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {

    if (F.getName() != "benchmarkBranch")
      return PreservedAnalyses::all();

    BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
    LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

    PRINT("Start of Pass", HIGH);

    PRINT("End of Pass", HIGH);
    return PreservedAnalyses::all();
  }
};

} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
           ArrayRef<PassBuilder::PipelineElement>) {
          if (Name == "fplicm-correctness") {
            FPM.addPass(HW2CorrectnessPass());
            return true;
          }
          return false;
        }
      );
    }
  };
}

