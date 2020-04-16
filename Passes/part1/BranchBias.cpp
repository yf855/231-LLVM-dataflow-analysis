#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/LLVMContext.h"

#include <map>
#include <vector>

using namespace llvm;
using namespace std;

namespace{
    struct BranchBias : public FunctionPass{
        static char ID;
        BranchBias() : FunctionPass(ID){}
        bool runOnFunction(Function &F) override{
            Module *M = F.getParent();
            LLVMContext &Context = M->getContext();

            FunctionCallee update_branch = M->getOrInsertFunction("updateBranchInfo", 
                                                                Type::getVoidTy(Context), 
                                                                Type::getInt1Ty(Context));
            FunctionCallee print_branch = M->getOrInsertFunction("printOutBranchInfo", 
                                                                Type::getVoidTy(Context));
            for (Function::iterator B=F.begin(),BE=F.end();B!=BE;++B){
                IRBuilder<> Builder (&*B);
                Instruction* I = (*B).getTerminator();
                if ((string) I->getOpcodeName()== "br" && (I->getNumOperands()>1)){
                    Value* has_taken = I->getOperand(0);
                    vector <Value*> args;
                    args.push_back(has_taken);
                    Builder.SetInsertPoint((*B).getTerminator());
                    Builder.CreateCall(update_branch,args);
                }
                if((string) I->getOpcodeName()== "ret"){
                    Builder.SetInsertPoint((*B).getTerminator());
                    Builder.CreateCall(print_branch);
                }
            }
            return false;
        }
    };
    
}
char BranchBias::ID = 0;
static RegisterPass<BranchBias> X("cse231-bb","Profiling Branch Bias",
                                    false,
                                    false);
