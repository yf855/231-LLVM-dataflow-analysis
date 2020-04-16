#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include <map>
#include <string>
using namespace llvm;
using namespace std;

namespace{

struct CountStaticInstr : public FunctionPass{
    static char ID;
    CountStaticInstr():FunctionPass(ID){}
    
    bool runOnFunction(Function &F) override{
	    map<string, int> useCount;
    
    //iterate over instructions
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
      string temp((*I).getOpcodeName());
      useCount[temp]++;
      //errs() << temp << "\n";
    }
    //print result from map
    for(auto it :useCount){
      errs() << it.first << "\t" << it.second << "\n";
    }
    //errs() <<"--------\n";
	return false;
    }

};  //end of struct
}

char CountStaticInstr::ID = 0;
static RegisterPass<CountStaticInstr> X("cse231-csi","CountStaticInstr",
	false,
	false);
