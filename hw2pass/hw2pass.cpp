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


using namespace llvm;
using namespace std;

namespace {

struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {

    if (F.getName() != "benchmarkBranch")
      return PreservedAnalyses::all();

    BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
    LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

#ifdef VERBOSE
    errs() << "\n** Dummy Insertion Pass End\n\n";
#endif

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

