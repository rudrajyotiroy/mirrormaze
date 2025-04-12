//===-- Updated LLVMSymmetricPass with Control Flow Analysis -----------===//
// Author : Rudrajyoti Roy, Anirudh Krishnan
// Last Stable Version : 10/04/25
// Run instruction : cd mirrormaze; ./compile.sh safeRSA; ./compile.sh unsafeRSA
// Progress : Attribute Detection, Taint Analysis, DDG generation

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
    bool hasEdge(const Instruction* from, const Instruction* to) const {
      auto it = Edges.find(from);
      if (it == Edges.end()) return false;
      return it->second.find(to) != it->second.end();
    }
  };

  struct SuperGraph {
    std::set<const Instruction*> Nodes;
    std::map<const Instruction*, std::set<const Instruction*>> Edges;

    // Get predecessors of a node
    std::set<const Instruction*> getPredecessors(const Instruction* I) const {
        std::set<const Instruction*> preds;
        for (const auto& pair : Edges) {
            if (pair.second.count(I))
                preds.insert(pair.first);
        }
        return preds;
    }

    // Get successors of a node
    std::set<const Instruction*> getSuccessors(const Instruction* I) const {
        auto it = Edges.find(I);
        if (it != Edges.end())
            return it->second;
        return {};
    }

    // Get root nodes (no incoming edges)
    std::set<const Instruction*> getRoots() const {
        std::set<const Instruction*> roots = Nodes;
        for (const auto& pair : Edges) {
            for (const Instruction* target : pair.second) {
                roots.erase(target); // If node has incoming edges, it's not a root
            }
        }
        return roots;
    }

    bool hasEdge(const Instruction* from, const Instruction* to) const {
      auto it = Edges.find(from);
      if (it == Edges.end()) return false;
      return it->second.find(to) != it->second.end();
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
                    if (annoStr.starts_with("secret")) {
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

    // // Debugging lines  
    // errs() << "Initial secret values:\n";
    // for (const Value* V : secretValues) {
    //     errs() << *V << "\n";
    // }
    // // Debugging lines

    std::set<Instruction*> secretBranches;
    // Propagation: iterate until no new secret values are discovered.
    bool changed = true;
    while (changed) {
      changed = false;
      
      // Iterate over all basic blocks and instructions.
      for (BasicBlock &BB : F) {
        for (Instruction &Inst : BB) {
          // Skip if the instruction is already marked as secret.
          // Debugging lines
          if (SwitchInst *SI = dyn_cast<SwitchInst>(&Inst)) {
            errs() << "Found switch instruction: " << Inst << "\n";
            errs() << "Switch operand: " << *SI->getCondition() << "\n";
            if (secretValues.count(SI->getCondition()) > 0) {
                errs() << "Switch is secret!\n";
            } else {
                errs() << "Switch is NOT secret!\n";
            }
        }
        // Debugging lines
        
          if (secretValues.count(&Inst))
            continue;
          
        //   for (unsigned op = 0; op < Inst.getNumOperands(); ++op) {
        //       if (secretValues.count(Inst.getOperand(op))) {
        //           secretValues.insert(&Inst);
        //           changed = true;
        //           errs() << "Tainted intermediate instruction: " << Inst << "\n";
        //           break;
        //       }
        //   }
        //   if (LoadInst *LI = dyn_cast<LoadInst>(&Inst)) {
        //     Value *pointerOperand = LI->getPointerOperand();
        //     if (secretValues.count(pointerOperand)) {
        //           secretValues.insert(&Inst); // The loaded value becomes tainted
        //           changed = true;
        //           errs() << "Tainted load: " << Inst << "\n";
        //           continue;
        //       }
        //   }
          
        //   if (StoreInst *SI = dyn_cast<StoreInst>(&Inst)) {
        //     Value *storedVal = SI->getValueOperand();
        //     if (secretValues.count(storedVal)) {
        //         Value *dest = SI->getPointerOperand();
        //         if (secretValues.insert(dest).second) {
        //             changed = true;
        //             errs() << "Tainted destination (store): " << *dest << "\n";
        //         }
        //     }
        // }

          // Check each operand; if any operand is secret, taint this instruction.
          bool tainted = false;
          for (unsigned op = 0; op < Inst.getNumOperands(); ++op) {
            //Debugging
            Value *operand = Inst.getOperand(op);
            errs() << "Inspecting operand: " << *operand << "\n";
            if (secretValues.count(operand) > 0) {
                errs() << "Operand is secret: " << *operand << "\n";
            }

            // Debugging
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
            //TODO : Does getParent capture all data dependencies??
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

    // This is if you merge all DDGS together, This function is a placeholder temo to ensure tests for insertion is correct
    SuperGraph mergeDDGs(const std::vector<DataDependenceGraph>& ddgs) {
      SuperGraph supergraph;
  
      for (const auto& ddg : ddgs) {
          // Add all nodes from the DDG into the supergraph
          for (const auto* node : ddg.Nodes) {
              supergraph.Nodes.insert(node);
          }
  
          // Add all edges from the DDG into the supergraph
          for (const auto& edge : ddg.Edges) {
              const Instruction* from = edge.first;
              for (const Instruction* to : edge.second) {
                  supergraph.Edges[from].insert(to);
              }
          }
      }
  
      return supergraph;
  }

    

  

    void expandDDGToSupergraph(
      const SuperGraph &supergraph,                 // Assume this is your target reference graph
      DataDependenceGraph &ddg,                     // Current per-block DDG
      const Instruction *superNode,                 // Node in supergraph we are processing
      std::map<const Instruction*, Instruction*> &ddgNodeMap, // Map Supergraph node → corresponding DDG node
      IRBuilder<> &Builder                          // Builder for IR insertion
  ) {
      // Check: is this node already in the DDG?
      if (ddgNodeMap.find(superNode) == ddgNodeMap.end()) {
          // --- Case 1: Dummy at root (no predecessors in supergraph) ---
          auto preds = supergraph.getPredecessors(superNode);
          Instruction *newDummy = nullptr;
          if (preds.empty()) {
              // Use any constant input
              Value *dummyInput = ConstantInt::get(Type::getInt32Ty(Builder.getContext()), 0);
              auto *dummyValueRoot = Builder.CreateAdd(dummyInput, dummyInput, "dummy_root");
              newDummy = dyn_cast<Instruction>(dummyValueRoot);

              errs() << "Inserted dummy at root: " << *newDummy << "\n";
          } 
          // --- Case 2: Dummy in middle of graph ---
          else {
              // Recursively ensure predecessors exist
              for (const Instruction *pred : preds) {
                  expandDDGToSupergraph(supergraph, ddg, pred, ddgNodeMap, Builder);
              }
  
              // Pick any available predecessor in DDG as operand
              const Instruction *anyPred = *preds.begin();
              Instruction *mappedPred = ddgNodeMap[anyPred];
  
              // Create dummy instruction using predecessor as operand
              auto *dummyValueInner = Builder.CreateAdd(mappedPred, ConstantInt::get(Type::getInt32Ty(Builder.getContext()), 0), "dummy_inner");
              newDummy = dyn_cast<Instruction>(dummyValueInner);

              errs() << "Inserted dummy in middle: " << *newDummy << "\n";
  
              // Add edges in DDG representation (optional, for DOT export update)
              ddg.addNode(newDummy);
              ddg.addEdge(mappedPred, newDummy);
          }
  
          // Update map: supergraph node → new dummy IR instruction
          ddgNodeMap[superNode] = newDummy;
  
          // Also add to DDG nodes if not already
          ddg.addNode(newDummy);
      }
  
      Instruction *currentNode = ddgNodeMap[superNode];
  
      // Recurse into successors of this node in the supergraph
      for (const Instruction *succ : supergraph.getSuccessors(superNode)) {
          expandDDGToSupergraph(supergraph, ddg, succ, ddgNodeMap, Builder);
  
          // After recursive call, link current node to successor in DDG
          Instruction *succNode = ddgNodeMap[succ];
          if (!ddg.hasEdge(currentNode, succNode)) {
              ddg.addEdge(currentNode, succNode);
  
              // Optional: also create dummy operation to establish use-def chain
              auto *linkValue = Builder.CreateAdd(currentNode, ConstantInt::get(Type::getInt32Ty(Builder.getContext()), 0), "dummy_link");
              Instruction *linkOp = dyn_cast<Instruction>(linkValue);
              succNode->insertBefore(linkOp);

              errs() << "Inserted dummy link from " << *currentNode << " to " << *succNode << "\n";
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
    PRINT(llvm::Twine("Done finding secret arguments\n\n"), MED);
    PRINT(llvm::Twine("Run forward taint analysis...\n"), MED);
    

    std::set<Instruction*> secretBranches = runForwardTaintAnalysis(F, secretValues);
    if(secretBranches.size()){
      PRINT(llvm::Twine("Detected secret branch...\n"), MED);
    } else{
      PRINT(llvm::Twine("Detected no secret branches, exiting...\n"), MED);
      return PreservedAnalyses::all();
    }

    std::vector<DataDependenceGraph> allDDGs; // ✅ collect all DDGs here


    for (auto condInst : secretBranches) {
      // If the branch is an if–else, there are two successors.
      PRINT(("Onto condition..."), LOW);
      if (BranchInst *BI = dyn_cast<BranchInst>(condInst)){
        BasicBlock *termBB = nullptr;
        unsigned numSucc = BI->getNumSuccessors();
        for (unsigned idx = 0; idx < numSucc; ++idx) {
          PRINT(("Onto successor %d", idx), LOW);
          BasicBlock *succ = BI->getSuccessor(idx);
          bool fallThrough = false;
          for (BasicBlock *term : successors(succ)) {
            if(termBB == nullptr){
              termBB = term;
            } 
            if (termBB != term){
              PRINT("Fallthrough detected", LOW); //TODO : Handling will be required while adding dummy code (entire supertree can be added without insertion)
              fallThrough = true;
            }
          }
          if (!fallThrough){
            DataDependenceGraph ddg;
            buildDDGForBasicBlock(succ, ddg, condInst);
            // Generate a filename that encodes the function name and branch.
            std::string FileName = F.getName().str() + "_ddg_" + succ->getName().str() + ".dot";
            dumpDDG(ddg, FileName);
            allDDGs.push_back(ddg);
            // // Anirudh added this: 
            // SuperGraph supergraph = mergeDDGs(allDDGs); // ✅ Build merged SuperGraph
            // std::map<const Instruction*, Instruction*> ddgNodeMap;
            // IRBuilder<> Builder(&*succ->getTerminator()); // good insertion point

            // for (const Instruction* root : supergraph.getRoots()) {
            //     expandDDGToSupergraph(supergraph, ddg, root, ddgNodeMap, Builder);
            // }

            // // Dump the expanded graph
            // std::string ExpandedFileName = F.getName().str() + "_expanded_ddg_" + succ->getName().str() + ".dot";
            // dumpDDG(ddg, ExpandedFileName);
            // // What this does is invoke expandDDGToSupergraph. Supergraph needs to be build however before this and used at this point.
          }
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
          allDDGs.push_back(ddg);
        }
      }

    }

    // Build merged supergraph after collecting all DDGs
    SuperGraph supergraph = mergeDDGs(allDDGs);

    // For each original DDG, expand to supergraph
    int index = 0;
    for (auto& ddg : allDDGs) {
        if (ddg.Nodes.empty()) continue;

        std::map<const Instruction*, Instruction*> ddgNodeMap;

        // Use any instruction from the block as insertion point
        const Instruction* firstInst = *ddg.Nodes.begin();
        IRBuilder<> Builder(const_cast<Instruction*>(firstInst));

        for (const Instruction* root : supergraph.getRoots()) {
            expandDDGToSupergraph(supergraph, ddg, root, ddgNodeMap, Builder);
        }

        std::string ExpandedFileName = "expanded_ddg_" + std::to_string(index++) + ".dot";
        dumpDDG(ddg, ExpandedFileName);
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

