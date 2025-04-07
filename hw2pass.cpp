// //===-- Updated LLVMSymmetricPass with Control Flow Analysis -----------===//
// #include <iostream>
// #include "llvm/Analysis/CFG.h"
// #include "llvm/Analysis/LoopInfo.h"
// #include "llvm/Analysis/BlockFrequencyInfo.h"
// #include "llvm/IR/Instructions.h"
// #include "llvm/IR/PassManager.h"
// #include "llvm/Passes/PassBuilder.h"
// #include "llvm/Support/raw_ostream.h"
// #include "llvm/Transforms/Utils/BasicBlockUtils.h"
// #include "llvm/IR/Constants.h"
// #include "llvm/IR/IRBuilder.h"
// #include "llvm/Passes/PassPlugin.h"


// using namespace llvm;
// using namespace std;

// namespace {

// struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

//   bool isTwoWayBranch(BasicBlock &BB) {
//     Instruction *TI = BB.getTerminator();
//     errs() << "HERE 1\n";
//     return isa<BranchInst>(TI) && cast<BranchInst>(TI)->isConditional();
//   }

//   BasicBlock *getLongerBlock(BasicBlock *A, BasicBlock *B) {
//     return A->size() >= B->size() ? A : B;
//   }

//   BasicBlock *getShorterBlock(BasicBlock *A, BasicBlock *B) {
//     return A->size() < B->size() ? A : B;
//   }

//   void alignInstructions(BasicBlock *Target, BasicBlock *Reference) {
//     IRBuilder<> Builder(Target->getTerminator());

//     errs() << "Start of AlignInstr fn\n";
//     for (Instruction &I : *Reference) {
//       errs() << "Entering particular ref\n";
//       if (I.isTerminator()) continue;
//       if (I.getType()->isVoidTy()) continue;
//       errs() << "Adding instr\n";
//       switch (I.getOpcode()) {
//         case Instruction::Add:
//           Builder.CreateAdd(ConstantInt::get(I.getType(), 0), ConstantInt::get(I.getType(), 0), "dummy_add");
//           break;
//         case Instruction::Sub:
//           Builder.CreateSub(ConstantInt::get(I.getType(), 0), ConstantInt::get(I.getType(), 0), "dummy_sub");
//           break;
//         case Instruction::Mul:
//           Builder.CreateMul(ConstantInt::get(I.getType(), 1), ConstantInt::get(I.getType(), 1), "dummy_mul");
//           break;
//         default:
//           Builder.CreateBitCast(Constant::getNullValue(I.getType()), I.getType(), "dummy_cast");
//           break;
//       }
//     }
//   }

//   PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {

//     if (F.getName() != "benchmarkBranch")
//       return PreservedAnalyses::all();

//     BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
//     LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);

// #ifdef VERBOSE
//     errs() << "\n\n** Dummy Insertion Pass Start\n";
// #endif

//     BasicBlock *SecretBB = nullptr;
//     BasicBlock *TargetBB = nullptr;

//     errs() << "\n\n** Dummy Insertion Pass Start\n";

//     for (BasicBlock &BB : F) {
//       if (!isTwoWayBranch(BB)) continue;

//       BranchInst *BI = cast<BranchInst>(BB.getTerminator());
//       BasicBlock *Succ0 = BI->getSuccessor(0);
//       BasicBlock *Succ1 = BI->getSuccessor(1);

//       BasicBlock *Shorter = getShorterBlock(Succ0, Succ1);
//       BasicBlock *Longer = getLongerBlock(Succ0, Succ1);

//       SecretBB = Shorter;
//       TargetBB = Longer;
//       errs() << "IDENTIFIED LONGER PATH\n";
//       break; // only handle first two-way branch for now
//     }

//     if (!SecretBB || !TargetBB) {
//       errs() << "Warning: Could not find conditional branch with distinguishable target blocks in function " << F.getName() << "\n";
//       return PreservedAnalyses::all();
//     }

//     IRBuilder<> Builder(SecretBB->getTerminator());
//     for (Instruction &I : *TargetBB) {
//       if (I.isTerminator())
//         continue;
//       switch (I.getOpcode()) {
//         case Instruction::Add: {
//           if (I.getType()->isIntegerTy()) {
//             auto *Zero = ConstantInt::get(cast<IntegerType>(I.getType()), 0);
//             Builder.CreateAdd(Zero, Zero, "dummy_add");
//           }
//           break;
//         }
//         case Instruction::Sub: {
//           if (I.getType()->isIntegerTy()) {
//             auto *Zero = ConstantInt::get(cast<IntegerType>(I.getType()), 0);
//             Builder.CreateSub(Zero, Zero, "dummy_sub");
//           }
//           break;
//         }
//         case Instruction::Mul: {
//           if (I.getType()->isIntegerTy()) {
//             auto *One = ConstantInt::get(cast<IntegerType>(I.getType()), 1);
//             Builder.CreateMul(One, One, "dummy_mul");
//           }
//           break;
//         }
//         default: {
//           if (!I.getType()->isVoidTy()) {
//             Builder.CreateBitCast(Constant::getNullValue(I.getType()), I.getType(), "dummy_bitcast");
//           }
//           break;
//         }
//       }
//     }

// #ifdef VERBOSE
//     errs() << "\n** Dummy Insertion Pass End\n\n";
// #endif

//     return PreservedAnalyses::none();
//   }
// };

// struct HW2PerformancePass : public PassInfoMixin<HW2PerformancePass> {
//   PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
//     BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
//     LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
//     return PreservedAnalyses::all();
//   }
// };

// } // namespace

// extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
//   return {
//     LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
//     [](PassBuilder &PB) {
//       PB.registerPipelineParsingCallback(
//         [](StringRef Name, FunctionPassManager &FPM,
//            ArrayRef<PassBuilder::PipelineElement>) {
//           if (Name == "fplicm-correctness") {
//             FPM.addPass(HW2CorrectnessPass());
//             return true;
//           }
//           if (Name == "fplicm-performance") {
//             FPM.addPass(HW2PerformancePass());
//             return true;
//           }
//           return false;
//         }
//       );
//     }
//   };
// }

