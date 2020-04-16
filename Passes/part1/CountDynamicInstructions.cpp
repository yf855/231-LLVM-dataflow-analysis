#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"


#include <map>
#include <vector>

using namespace llvm;
using namespace std;

namespace {
    struct CountDynamicInstructions : public FunctionPass {
        static char ID;
        CountDynamicInstructions() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            Module *M = F.getParent();
            LLVMContext &Context = M->getContext();

            //get function from module
            FunctionCallee update_func = M->getOrInsertFunction("updateInstrInfo", Type::getVoidTy(Context), 
                                                                Type::getInt32Ty(Context), 
                                                                Type::getInt32PtrTy(Context), 
                                                                Type::getInt32PtrTy(Context));
            FunctionCallee print_func = M->getOrInsertFunction("printOutInstrInfo", Type::getVoidTy(Context));

            // Iterate through basic blocks
            for (Function::iterator B = F.begin(), BE = F.end(); B != BE; ++B) {
                IRBuilder<> Builder(&*B);
                map<uint32_t, uint32_t> useCount;
    
                // Iterate through instructions
                for (BasicBlock::iterator I = B->begin(), IE = B->end(); I != IE; ++I) {
                    useCount[(uint32_t)(*I).getOpcode()]++;
                }                

                int num = useCount.size();
                vector<Value *> args;
                args.push_back(ConstantInt::get(Type::getInt32Ty(Context), num));

                vector<uint32_t> keys;
                vector<uint32_t> values;
                ArrayType* ArrTy = ArrayType::get(IntegerType::get(F.getContext(), 32), num);

                for (auto it :useCount) {
                    keys.push_back(it.first);
                    values.push_back(it.second);
                }

                GlobalVariable *GK = new GlobalVariable(*M, 
                    ArrTy, 
                    true, 
                    GlobalVariable::InternalLinkage, 
                    ConstantDataArray::get(Context, *(new ArrayRef<uint32_t>(keys))), 
                    "GlobalKeys");
                GlobalVariable *GV = new GlobalVariable(*M, 
                    ArrTy, 
                    true, 
                    GlobalVariable::InternalLinkage, 
                    ConstantDataArray::get(Context, *(new ArrayRef<uint32_t>(values))), 
                    "GlobalValues");
                
                args.push_back(Builder.CreatePointerCast(GK, Type::getInt32PtrTy(Context)));
                args.push_back(Builder.CreatePointerCast(GV, Type::getInt32PtrTy(Context)));

                //now go to the end of each block to update 
                Builder.SetInsertPoint((*B).getTerminator());
                Builder.CreateCall(update_func, args);

                //go to the end of each block and see if it is a return function
                if ((string) ((*B).getTerminator())->getOpcodeName() == "ret") {
                    Builder.SetInsertPoint((*B).getTerminator());
                    Builder.CreateCall(print_func);
                }

            }

            return false;
        }
    }; // end of struct
}  

char CountDynamicInstructions::ID = 0;
static RegisterPass<CountDynamicInstructions> X("cse231-cdi", "Counting Dynamic Instructions",
                             false,
                             false);