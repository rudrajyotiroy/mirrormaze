//===-- Updated LLVMSymmetricPass with Control Flow Analysis -----------===//
// Author : Rudrajyoti Roy
// Last Stable Version : 10/04/25
// Run instruction : cd mirrormaze; ./compile.sh safeRSA; ./compile.sh unsafeRSA
// Progress : Attribute Detection, Taint Analysis, DDG generation

#include <iostream>
#include <string>
#include <fstream> 
#include <vector>
#include <sstream>
#include "llvm/Support/raw_ostream.h"
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
// #define LEGACY_LLVM

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
  public:
  // Constructor accepting an argument
    HW2CorrectnessPass(bool option) : optimizeSupergraph_(option) {}

  // Anirudh : I am currently implementing 1 , can do 2 . Just making code much cleaner
  enum DummyMode { ALL_DUMMY_OPERANDS, MIXED_OPERANDS };


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

  // Anirudh : Added SuperGraph struct to define the supergraph
  struct SuperGraph {
    std::set<const Instruction*> Nodes;
    std::map<const Instruction*, std::set<const Instruction*>> Edges;
  
    void addNode(const Instruction *I) {
      Nodes.insert(I);
    }
  
    void addEdge(const Instruction *From, const Instruction *To) {
      Edges[From].insert(To);
    }
  
    // Utility: Get predecessors of a node
    std::set<const Instruction*> getPredecessors(const Instruction* I) const {
      std::set<const Instruction*> preds;
      for (const auto& pair : Edges) {
        if (pair.second.count(I)) preds.insert(pair.first);
      }
      return preds;
    }

  
    // Utility: Get successors of a node
    std::set<const Instruction*> getSuccessors(const Instruction* I) const {
      auto it = Edges.find(I);
      if (it != Edges.end()) return it->second;
      return {};
    }
  
    // Utility: Get root nodes
    std::set<const Instruction*> getRoots() const {
      std::set<const Instruction*> roots = Nodes;
      for (const auto& pair : Edges) {
        for (const Instruction* target : pair.second) {
          roots.erase(target); // Remove nodes that have incoming edges
        }
      }
      return roots;
    }
  };
  
  // Anirudh: Giving this a seperate function for cleaner code , and easier readablity.
  void dumpSuperGraph(const SuperGraph& supergraph, const std::string& FileName) {
    std::error_code EC;
    raw_fd_ostream file(FileName, EC, sys::fs::OF_Text);
    if (EC) {
      errs() << "Error opening file " << FileName << " for writing SuperGraph.\n";
      return;
    }
  
    file << "digraph SuperGraph {\n";
    for (const Instruction *I : supergraph.Nodes) {
      file << "  \"" << I << "\" [label=\"" << I->getOpcodeName() << "\"];\n";
    }
    for (auto &pair : supergraph.Edges) {
      const Instruction *From = pair.first;
      for (const Instruction *To : pair.second) {
        file << "  \"" << From << "\" -> \"" << To << "\";\n";
      }
    }
    file << "}\n";
    file.close();
    errs() << "SuperGraph dumped to file: " << FileName << "\n";
  }

  // Anirudh: Placeholder merging function
  SuperGraph mergeDDGs(const std::vector<DataDependenceGraph>& allDDGs) {
    SuperGraph supergraph;

    for (const auto& ddg : allDDGs) {
        // Add all nodes from the DDG into the supergraph
        for (const auto* node : ddg.Nodes) {
            if (!node) {
                errs() << "Warning: Null node in DDG\n";
                continue;
            }
            supergraph.addNode(node);
        }

        // Add all edges from the DDG into the supergraph
        for (const auto& edge : ddg.Edges) {
            const Instruction* from = edge.first;
            for (const Instruction* to : edge.second) {
                supergraph.addEdge(from, to);
            }
        }
    }

    // Optional: Debug info
    errs() << "SuperGraph built: " << supergraph.Nodes.size() << " nodes, "
           << supergraph.Edges.size() << " edges.\n";

    return supergraph;
}

// Anirudh: This is the helper that adds instruction
Value* buildStructuredDummyFlow(IRBuilder<> &Builder,
                                const std::vector<std::string> &superGraphOps,
                                DummyMode mode = ALL_DUMMY_OPERANDS) {
    LLVMContext &Ctx = Builder.getContext();
    Value *dummyInput = Builder.getInt32(42); // Arbitrary dummy input
    Value *prevDummyRes = nullptr;

    for (const auto &opcode : superGraphOps) {
        Value *lhs = nullptr;
        Value *rhs = dummyInput;

        if (!prevDummyRes) {
            // First operation
            if (mode == ALL_DUMMY_OPERANDS) {
                lhs = dummyInput;
            } else if (mode == MIXED_OPERANDS) {
                // Optional: use dummyInput or safe constant or random operand
                lhs = dummyInput; // For now, safe choice
            }
        } else {
            lhs = prevDummyRes;
        }

        // Build operation based on opcode
        Value *result = nullptr;
        if (opcode == "add") {
            result = Builder.CreateAdd(lhs, rhs);
        } else if (opcode == "mul") {
            result = Builder.CreateMul(lhs, rhs);
        } else if (opcode == "xor") {
            result = Builder.CreateXor(lhs, rhs);
        } else if (opcode == "load") {
            Value *dummyPtr = Builder.CreateAlloca(Type::getInt32Ty(Ctx));
            result = Builder.CreateLoad(Type::getInt32Ty(Ctx), dummyPtr);
        } else if (opcode == "store") {
            Value *dummyPtr = Builder.CreateAlloca(Type::getInt32Ty(Ctx));
            Builder.CreateStore(rhs, dummyPtr, true); // volatile store
            result = rhs; // Chain forward dummyInput
        } else {
            // Fallback: default to add
            result = Builder.CreateAdd(lhs, rhs);
        }

        prevDummyRes = result;

        
        for (const auto &opcode : superGraphOps) {
            errs() << "  Dummy operation: " << opcode << "\n";
        }

    }

    return prevDummyRes; // Final dummy result (if you want to use or ignore)
}

  // Anirudh: Helper for helper lol
  std::vector<std::string> extractSuperGraphOpSequence(const SuperGraph &supergraph) {
  std::vector<std::string> opSequence;
  for (const Instruction *I : supergraph.Nodes) {
      opSequence.push_back(I->getOpcodeName());
  }
  return opSequence;
  }



  // Ani B - snippet to run python script
  void runPythonMergeScript(const std::string &searchPattern, size_t secretGraphIndex) {
    std::string command = "python3  ../../hw2pass/merge_ddg.py " + searchPattern;
        // + " " + std::to_string(secretGraphIndex);
    int ret = std::system(command.c_str());
    if(ret != 0) {
      llvm::errs() << "Error: Python merge_ddg.py script returned non-zero exit code: " << ret << "\n";
    } else {
      llvm::errs() << "Python merge_ddg.py script ran successfully. New file in " + searchPattern +"_supergraph.dot" + " with secret index=" << secretGraphIndex << "\n";
    }
  }

  static std::vector<std::string> parseSupergraphDot(const std::string &dotPath) {
  std::vector<std::string> opSeq;
  std::ifstream in(dotPath);
  if (!in.is_open()) {
    errs() << "Could not open supergraph file: " << dotPath << "\n";
    return opSeq;
  }

  std::string line;
  while (std::getline(in, line)) {
    auto p = line.find("label=\"");
    if (p == std::string::npos) continue;
    p += 7;
    auto q = line.find('"', p);
    if (q == std::string::npos) continue;
    std::string lbl = line.substr(p, q - p);
    // Skip raw addresses
    if (lbl.rfind("0x",0) == 0) continue;

    // If label contains '=', parse "<dst> = <opcode> ..."
    auto eqpos = lbl.find('=');
    if (eqpos != std::string::npos) {
      std::istringstream iss(lbl);
      std::string dst, eq, opcode;
      if ((iss >> dst >> eq >> opcode) && eq == "=") {
        opSeq.push_back(opcode);
      } else {
        errs() << "Skipping unparsable label: " << lbl << "\n";
      }
    } else {
      // No '=', so treat entire label as the opcode
      opSeq.push_back(lbl);
    }
  }

  return opSeq;
}


  static StringRef getAnnotationString(CallInst *CI) {
    // The second operand of llvm.var.annotation is the annotation string.
    Value *AnnoPtr = CI->getArgOperand(1);
    #ifdef LEGACY_LLVM
    if (auto *CE = dyn_cast<ConstantExpr>(AnnoPtr)) {
    if (auto *GV = dyn_cast<GlobalVariable>(CE->getOperand(0))) {
    #else
    AnnoPtr = AnnoPtr->stripPointerCasts();
    if (auto *GV = dyn_cast<GlobalVariable>(AnnoPtr)) {
    #endif
      if (auto *CDA = dyn_cast<ConstantDataArray>(GV->getInitializer()))
        return CDA->getAsString();
    }
    #ifdef LEGACY_LLVM
    }
    #endif
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
              if (called->getName().starts_with("llvm.var.annotation")) {
                StringRef annoStr = getAnnotationString(CI);
                PRINT(llvm::Twine("Annotation string is: ") + annoStr, LOW);
                if (annoStr.starts_with("secret")) {
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
                  if (called->getName().starts_with("llvm.var.annotation")) {
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
        file << "  \"" << I << "\" [label=\"" << I->getOpcodeName() << "\"];\n";
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

    // Use optimizeSupergraph_ as control to determine if supergraph should be optimized
    if(optimizeSupergraph_) {
      PRINT(llvm::Twine("====> Optimize the supergraph formation\n "), HIGH);
    } else {
      PRINT(llvm::Twine("====> Skip supergraph optimization\n "), HIGH);
    }
    if (F.getName() == "main"){
        PRINT(llvm::Twine("Skipping function ") + F.getName(), HIGH);
        return PreservedAnalyses::all();
    }

    std::vector<DataDependenceGraph> allDDGs;  // Anirudh: added this to store all DDGS before merging.
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

    // additions by Ani b 
    const Instruction *originalSecretInst = *secretBranches.begin();

    size_t secretGraphIdx = SIZE_MAX;
    size_t ddgIdx         = 0;
    bool   found          = false;
  
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
            allDDGs.push_back(ddg); // Anirudh: Stores each ddg

             // additions by Ani b 
            if (!found && condInst == originalSecretInst){
              secretGraphIdx = ddgIdx;
              found = true;
            }
            ++ddgIdx;
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
          allDDGs.push_back(ddg); // Anirudh: Stores each ddg

           // additions by Ani b 
          if (!found && condInst == originalSecretInst){
            secretGraphIdx = ddgIdx;
            found = true;
          }
          ++ddgIdx;
        }
      }

    }

    // calling the python script to generate the supergraph
    PRINT(F.getName().str(), LOW);

    PRINT(secretGraphIdx, LOW);

    runPythonMergeScript(F.getName().str(), secretGraphIdx);

    PRINT("End of Pass", HIGH);

    // supergraph flow from here - ideally call it from from F.getName().str() + "_supergraph.dot"
    std::string superDot = F.getName().str() + "_supergraph.dot";
    auto superGraphOps = parseSupergraphDot(superDot);
    if (superGraphOps.empty()) {
        errs() << "Warning: no opcodes parsed from " << superDot << "\n";
    }

    // SuperGraph supergraph = mergeDDGs(allDDGs);
    // dumpSuperGraph(supergraph, F.getName().str() + "_supergraph.dot");

    // Anirudh: This is the main dummy insertion loop
    // auto superGraphOps = extractSuperGraphOpSequence(supergraph);

    for (auto &ddg : allDDGs) {
        if (!ddg.Nodes.empty()) {
            const Instruction *anyInst = *ddg.Nodes.begin();
            BasicBlock *BB = const_cast<BasicBlock*>(anyInst->getParent());

            IRBuilder<> Builder(&*BB->getFirstInsertionPt());
            errs() << "Inserted dummy chain for block: " << BB->getName() << "\n";
            buildStructuredDummyFlow(Builder, superGraphOps, ALL_DUMMY_OPERANDS); // Start with safe mode

            // Anirudh: This is to verify that padding occurs and in correct amount
            size_t realOpCount = 0;
            for (const Instruction *I : ddg.Nodes) {
                unsigned opcode = I->getOpcode();
                if (Instruction::isBinaryOp(opcode) || isa<LoadInst>(I) || isa<StoreInst>(I) || isa<AllocaInst>(I)) {
                    realOpCount++;
                }
            }

            size_t dummyOpCount = superGraphOps.size() > realOpCount ? superGraphOps.size() - realOpCount : 0;
            size_t superGraphOpCount = superGraphOps.size();

            errs() << "Verification for DDG in block: " << BB->getName() << "\n";
            errs() << "  Real Ops: " << realOpCount << "\n";
            errs() << "  Dummy Ops: " << dummyOpCount << "\n";
            errs() << "  SuperGraph Ops: " << superGraphOpCount << "\n";
            assert(realOpCount + dummyOpCount == superGraphOpCount); // can remove previous statement. 
        }
    }
    return PreservedAnalyses::all();
  }
  private:
  bool optimizeSupergraph_;
};



} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
           ArrayRef<PassBuilder::PipelineElement>) {
          if (Name == "stacked") {
            FPM.addPass(HW2CorrectnessPass(false));
            return true;
          }
          if (Name == "merged") {
            FPM.addPass(HW2CorrectnessPass(true));
            return true;
          }
          return false;
        }
      );
    }
  };
}
