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

#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Casting.h"

#include <set>
#include <functional>


enum ImportanceLevel {
    NONE = 0,  // No messages are logged.
    HIGH = 1,  // Only high-importance messages.
    MED  = 2,  // Medium-importance messages.
    LOW  = 3,  // Low-importance messages.
    ALL  = 4   // All messages are logged.
};

// Change here
#define VERBOSE LOW 

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
static StringRef getAnnotationString(CallInst *CI) {
  // The second operand of llvm.var.annotation is the annotation string.
  Value *AnnoPtr = CI->getArgOperand(1);
  if (auto *CE = dyn_cast<ConstantExpr>(AnnoPtr)) {
    if (auto *GV = dyn_cast<GlobalVariable>(CE->getOperand(0))) {
      if (auto *CDA = dyn_cast<ConstantDataArray>(GV->getInitializer()))
        return CDA->getAsString();
    }
  }
  return "";
}
// isSecretArgument: Returns true if the given function argument is annotated with "secret".
bool isSecretArgument(Function &F, Argument &arg) {
  PRINT(llvm::Twine("Entered isSecretArgument for argument: ") + arg.getName(), MED);
  
  // Iterate over the instructions in the function's entry block.
  for (Instruction &I : F.getEntryBlock()) {
    if (auto *AI = dyn_cast<AllocaInst>(&I)) {
      PRINT(llvm::Twine("Examining alloca: ") + AI->getName(), LOW);
      
      // Check if this alloca stores our argument.
      bool storesArg = false;
      for (User *U : AI->users()) {
        if (auto *store = dyn_cast<StoreInst>(U)) {
          PRINT("Found store instruction on alloca.", LOW);
          if (store->getValueOperand() == &arg) {
            PRINT(llvm::Twine("Store matches argument: ") + arg.getName(), LOW);
            storesArg = true;
            break;
          }
        }
      }
      if (!storesArg) {
        PRINT(llvm::Twine("Alloca ") + AI->getName() + " does not store argument.", LOW);
        continue;
      }
      
      // Now, check for annotation calls associated with the alloca.
      for (User *U : AI->users()) {
        // Direct call to llvm.var.annotation.
        if (auto *CI = dyn_cast<CallInst>(U)) {
          if (Function *called = CI->getCalledFunction()) {
            PRINT(llvm::Twine("Found call instruction: ") + called->getName(), LOW);
            if (called->getName() == "llvm.var.annotation") {
              StringRef annoStr = getAnnotationString(CI);
              PRINT(llvm::Twine("Annotation string is: ") + annoStr, LOW);
              if (annoStr.equals("secret")) {
                PRINT("Found secret annotation directly on alloca.", LOW);
                return true;
              }
            }
          }
        }
        // If a bitcast is present, check its users.
        if (auto *BC = dyn_cast<BitCastInst>(U)) {
          PRINT(llvm::Twine("Found bitcast instruction on alloca: ") + BC->getName(), LOW);
          for (User *V : BC->users()) {
            if (auto *CI = dyn_cast<CallInst>(V)) {
              if (Function *called = CI->getCalledFunction()) {
                PRINT(llvm::Twine("Found call instruction on bitcast: ") + called->getName(), LOW);
                if (called->getName() == "llvm.var.annotation") {
                  StringRef annoStr = getAnnotationString(CI);
                  PRINT(llvm::Twine("Annotation string from bitcast is: ") + annoStr, LOW);
                  if (annoStr.startswith("secret")) {
                    PRINT("Found secret annotation on bitcast.", LOW);
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}


  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {

    if (F.getName() == "main"){
        PRINT(llvm::Twine("Skipping function ") + F.getName(), HIGH);
        return PreservedAnalyses::all();
    }

    BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
    LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

    PRINT(llvm::Twine("Start of Pass for function ") + F.getName(), HIGH);

    // Collect inputs (arguments) with the "secret" attribute.
    std::set<const Value*> secretValues;
    
    for (Argument &arg : F.args()) {
      // Check for a named attribute using the function's attribute list.
      PRINT(llvm::Twine("Checking if current arg is secret"), LOW);
      if (isSecretArgument(F, arg)) {
        secretValues.insert(&arg);
        // Use llvm::Twine to concatenate the message.
        PRINT(llvm::Twine("Found secret argument: ") + arg.getName(), MED);
      }
    }
    PRINT(llvm::Twine("Done finding secret arguments"), LOW);

    // Helper lambda that recursively checks if a given value depends on a secret.
    std::function<bool(const Value*, std::set<const Value*>&)> dependsOnSecretRec =
      [&](const Value* v, std::set<const Value*>& visited) -> bool {
        if (secretValues.count(v))
          return true;
        if (visited.count(v))
          return false;
        visited.insert(v);
        if (const Instruction* inst = dyn_cast<Instruction>(v)) {
          for (const Use &U : inst->operands()) {
            if (dependsOnSecretRec(U.get(), visited))
              return true;
          }
        }
        return false;
      };

    // A lambda wrapper that initializes the visited set.
    auto dependsOnSecret = [&](const Value* v) -> bool {
      std::set<const Value*> visited;
      return dependsOnSecretRec(v, visited);
    };

    // Iterate over all basic blocks looking for conditional branches.
    for (BasicBlock &BB : F) {
      PRINT(llvm::Twine("Entering basic block"), LOW);
      if (BranchInst *branch = dyn_cast<BranchInst>(BB.getTerminator())) {
        if (branch->isConditional()) {
          PRINT(llvm::Twine("Entering conditional branch"), LOW);
          Value *cond = branch->getCondition();
          if (dependsOnSecret(cond)) {
            // Optionally, get the debug line number if available.
            unsigned line = 0;
            if (DILocation *loc = branch->getDebugLoc())
              line = loc->getLine();

            // Use llvm::Twine and std::to_string() to build the message.
            PRINT(llvm::Twine("Conditional branch depending on secret found at line ") + std::to_string(line), LOW);
          }
        }
      }
      
    }



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

