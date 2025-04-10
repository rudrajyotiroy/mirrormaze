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
using CondInstInfo = std::pair<const Instruction*, std::vector<const BasicBlock*>>;

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
    return false;
  }
/*
  bool dependsOnSecretHelper(const Value *v, const std::set<const Value*> &secretValues, 
                           std::set<const Value*> &visited) {
    // If this value is one of our secret variables, return true.
    errs() << "\n\n";
    // PRINT("Helper entry", LOW);
    if (secretValues.count(v)) {
      errs() << "Found secret variable: " 
            << (v->hasName() ? v->getName() : "<unnamed>") << "\n";
      return true;
    }
    
    // Prevent cycles.
    if (visited.count(v))
      return false;
    visited.insert(v);

    // If this value is an instruction, check all its operands.
    if (const Instruction *I = dyn_cast<Instruction>(v)) {
      errs() << "Inspecting instruction: " 
            << I->getOpcodeName() << " in block " 
            << I->getParent()->getName() << "\n";
      for (unsigned i = 0; i < I->getNumOperands(); i++) {
        const Value *op;    
        if (auto *LI = dyn_cast<LoadInst>(I)) {
          PRINT("Load instr", LOW);
          op = LI->getPointerOperand();
        }
        else{
          PRINT("Non-Load instr", LOW);
          op = I->getOperand(i);
        }
        errs() << "  Checking operand " << i << ": " 
              << (op->hasName() ? op->getName() : "<unnamed>") << "\n";
        if (dependsOnSecretHelper(op, secretValues, visited))
          return true;
      }
    } else {
        errs() << "Value is not an instruction: " 
              << (v->hasName() ? v->getName() : "<unnamed>") << "\n";

      }
    
    return false;
  }

bool dependsOnSecret(const Value *v, const std::set<const Value*> &secretValues) {
  std::set<const Value*> visited;
  bool result = dependsOnSecretHelper(v, secretValues, visited);
  errs() << "Final dependency check for value " 
         << (v->hasName() ? v->getName() : "<unnamed>") 
         << " returns " << (result ? "true" : "false") << "\n";
  return result;
}
*/


  std::set<const Instruction*> runForwardTaintAnalysis(Function &F, std::set<const Value*> secretValues) {
    std::set<const Instruction*> secretBranches;
    // Propagation: iterate until no new secret values are discovered.
    bool changed = true;
    while (changed) {
      changed = false;
      
      // Iterate over all basic blocks and instructions.
      for (BasicBlock &BB : F) {
        for (Instruction &Inst : BB) {
          // Skip if the instruction is already marked as secret.
          if (secretValues.count(&Inst))
            continue;

          // Check each operand; if any operand is secret, taint this instruction.
          bool tainted = false;
          for (unsigned op = 0; op < Inst.getNumOperands(); ++op) {
            if (secretValues.count(Inst.getOperand(op)) > 0) {
              tainted = true;
              break;
            }
          }
          
          // If the instruction is tainted, update secret values.
          if (tainted) {
            secretValues.insert(&Inst);
            changed = true;
            errs() << "Tainted value: " << Inst << "\n";
            
            // Special handling: if the tainted instruction is a branch or switch.
            if (BranchInst *BI = dyn_cast<BranchInst>(&Inst)) {
              // For branch instructions, check if it is conditional.
              if (BI->isConditional()) {
                secretBranches.insert(BI);
                errs() << "Found secret branch: " << *BI << "\n";
              }
            } else if (SwitchInst *SI = dyn_cast<SwitchInst>(&Inst)) {
              secretBranches.insert(SI);
              errs() << "Found secret switch: " << *SI << "\n";
            } else if (StoreInst *SI = dyn_cast<StoreInst>(&Inst)) {
              // Check if the value being stored is secret.
              if (secretValues.count(SI->getValueOperand()) > 0) {
                Value *dest = SI->getPointerOperand();
                // Only add if not already tainted.
                if (secretValues.insert(dest).second) {
                  changed = true;
                  errs() << "Tainted destination: " << *dest << "\n";
                }
              }
            }
          }
        }
      }
    }

    // Optionally, output results.
    errs() << "\nFinal set of secret values:\n";
    for (const Value *V : secretValues) {
      errs() << *V << "\n";
    }
    errs() << "\nSecret branches/switches:\n";
    for (const Instruction *I : secretBranches) {
      errs() << *I << "\n";
    }

    return secretBranches;
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
    PRINT(llvm::Twine("Done finding secret arguments\n\n"), MED);
    PRINT(llvm::Twine("Run forward taint analysis...\n"), MED);
    

    std::vector<CondInstInfo> secretCondBranches;
    std::set<const Instruction*> secretBranches = runForwardTaintAnalysis(F, secretValues);

    // Iterate over all basic blocks in the function.
    // for (BasicBlock &BB : F) {
    //   Instruction *TI = BB.getTerminator();
    //   if (!TI)
    //     continue; // TODO?

    //   // Check if the terminator is a BranchInst.
    //   if (auto *branch = dyn_cast<BranchInst>(TI)) {
    //     // Only consider conditional branches.
    //     if (branch->isConditional()) {
    //       PRINT(llvm::Twine("Entering conditional branch in block ") + BB.getName(), LOW);
          
    //       // Collect successors.
    //       std::vector<const BasicBlock*> successors;
    //       for (unsigned i = 0; i < branch->getNumSuccessors(); i++) {
    //         successors.push_back(branch->getSuccessor(i));
    //         PRINT(llvm::Twine("Successor ") + std::to_string(i) + ": " +
    //               branch->getSuccessor(i)->getName(), LOW);
    //       }
    //       // Store the branch and its successors.
    //       secretCondBranches.push_back(std::make_pair(branch, successors));

    //       // Check if condition depends on secret.
    //       Value *cond = branch->getCondition();
    //       if (dependsOnSecret(cond, secretValues)) {
    //         unsigned line = 0;
    //         if (DILocation *loc = branch->getDebugLoc())
    //           line = loc->getLine();
    //         PRINT(llvm::Twine("Conditional branch depending on secret found at line ") +
    //               std::to_string(line), LOW);
    //       }
    //     }
    //   }
    //   // Check if the terminator is a SwitchInst.
    //   else if (auto *SI = dyn_cast<SwitchInst>(TI)) {
    //     PRINT(llvm::Twine("Entering switch statement in block ") + BB.getName(), LOW);
        
    //     std::vector<const BasicBlock*> successors;
    //     // Store the default destination first.
    //     successors.push_back(SI->getDefaultDest());
    //     PRINT("Default destination: " + SI->getDefaultDest()->getName(), LOW);
        
    //     // Iterate over each case.
    //     unsigned numCases = SI->getNumCases();
    //     for (unsigned i = 0; i < numCases; ++i) {
    //       BasicBlock *caseDest = SI->getSuccessor(i);
    //       successors.push_back(caseDest);
    //       // For more information, you could also extract and print the case value:
    //       // ConstantInt *caseVal = SI->findCaseValue(i);
    //       // PRINT(llvm::Twine("Case ") + std::to_string(i) + " with value " +
    //       //       caseVal->getValue().toString(10, true) + " goes to: " +
    //       //       caseDest->getName(), LOW);
    //     }
    //     // Store the switch and its successors.
    //     secretCondBranches.push_back(std::make_pair(SI, successors));

    //     // Check the switch condition for secret dependency.
    //     Value *cond = SI->getCondition();
    //     if (dependsOnSecret(cond, secretValues)) {
    //       unsigned line = 0;
    //       if (DILocation *loc = SI->getDebugLoc())
    //         line = loc->getLine();
    //       PRINT(llvm::Twine("Switch statement depending on secret found at line ") +
    //             std::to_string(line), LOW);
    //     }
    //   }
    // }



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

