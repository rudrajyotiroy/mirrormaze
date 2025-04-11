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
#include "llvm/Support/FileSystem.h"

// #include "llvm/Analysis/DDG.h"
// #include "llvm/Analysis/DependenceAnalysis.h"

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

  struct DataDependenceGraph {
    std::set<const Instruction*> Nodes;
    std::map<const Instruction*, std::set<const Instruction*>> Edges;
    void addNode(const Instruction *I) {
      Nodes.insert(I);
    }
    void addEdge(const Instruction *From, const Instruction *To) {
      Edges[From].insert(To);
    }
  };

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

  std::set<Instruction*> runForwardTaintAnalysis(Function &F, std::set<const Value*> secretValues) {
    std::set<Instruction*> secretBranches;
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

  // Build the data-dependence graph for a given basic block.
    // For every instruction in the block, add an edge from an instruction defining a variable to
    // an instruction that uses it. This example limits itself to instructions in the same block.
    // Also, a control dependency edge is added from the conditional instruction to the first
    // instruction of the block.
    void buildDDGForBasicBlock(BasicBlock *BB, DataDependenceGraph &ddg,
                               const Instruction *condInst) {
      // If the block is not empty, add a control edge from the secret-dependent branch instruction
      // to the block's first instruction.
      if (!BB->empty()) {
        Instruction *firstInst = &*(BB->begin());
        ddg.addNode(firstInst);
        ddg.addEdge(condInst, firstInst);
      }
      // Process each instruction in the basic block.
      for (Instruction &I : *BB) {
        ddg.addNode(&I);
        // For each operand of 'I', if the operand is defined by an instruction in BB, add a def-use edge.
        for (unsigned op = 0; op < I.getNumOperands(); ++op) {
          if (Instruction *defInst = dyn_cast<Instruction>(I.getOperand(op))) {
            if (defInst->getParent() == BB)
              ddg.addEdge(defInst, &I);
          }
        }
      }
    }

    // Dump the data-dependence graph in DOT format to a file.
    void dumpDDG(const DataDependenceGraph &ddg, const std::string &FileName) {
      std::error_code EC;
      raw_fd_ostream file(FileName, EC, sys::fs::OF_Text);
      if (EC) {
        errs() << "Error opening file " << FileName << " for writing DDG.\n";
        return;
      }
      file << "digraph DDG {\n";
      // For each node, write out a node label.
      for (const Instruction *I : ddg.Nodes) {
        // We use the pointer value as the node identifier and print the instruction as its label.
        file << "  \"" << I << "\" [label=\"" << *I << "\"];\n";
      }
      // Output all edges.
      for (auto &pair : ddg.Edges) {
        const Instruction *From = pair.first;
        for (const Instruction *To : pair.second)
          file << "  \"" << From << "\" -> \"" << To << "\";\n";
      }
      file << "}\n";
      file.close();
      errs() << "DDG dumped to file: " << FileName << "\n";
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
    

    std::set<Instruction*> secretBranches = runForwardTaintAnalysis(F, secretValues);
    if(secretBranches.size()){
      PRINT(llvm::Twine("Detected secret branch...\n"), MED);
    } else{
      PRINT(llvm::Twine("Detected no secret branches, exiting...\n"), MED);
      return PreservedAnalyses::all();
    }

    for (auto condInst : secretBranches) {
      // If the branch is an if–else, there are two successors.
      PRINT(("Onto condition..."), LOW);
      if (BranchInst *BI = dyn_cast<BranchInst>(condInst)){
        unsigned numSucc = BI->getNumSuccessors();
        for (unsigned idx = 0; idx < numSucc; ++idx) {
          PRINT(("Onto successor %d", idx), LOW);
          BasicBlock *succ = BI->getSuccessor(idx);
          DataDependenceGraph ddg;
          buildDDGForBasicBlock(succ, ddg, condInst);
          // Generate a filename that encodes the function name and branch.
          std::string FileName = F.getName().str() + "_ddg_" + succ->getName().str() + ".dot";
          dumpDDG(ddg, FileName);
        }
      }
      if (SwitchInst *SI = dyn_cast<SwitchInst>(condInst)) {
        unsigned numSucc = SI->getNumSuccessors();
        for (unsigned idx = 0; idx < numSucc; ++idx) {
          PRINT(("Onto successor %d", idx), LOW);
          BasicBlock *succ = SI->getSuccessor(idx);
          DataDependenceGraph ddg;
          buildDDGForBasicBlock(succ, ddg, condInst);
          // Generate a filename that encodes the function name and the successor block.
          std::string FileName = F.getName().str() + "_ddg_" + succ->getName().str() + ".dot";
          dumpDDG(ddg, FileName);
        }
      }

    }

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

