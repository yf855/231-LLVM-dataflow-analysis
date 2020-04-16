#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constant.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/ConstantFolder.h"
#include "231DFA.h"
#include "llvm/IR/IRBuilder.h"
#include <map>
#include <set>
#include <string> 
#include <unordered_map>
#include <iostream>
using namespace llvm;
using namespace std;
enum ConstState{Bottom, Const, Top};
typedef struct Const_{
    ConstState state; 
    Constant * value;
    bool operator!=(Const_& rhs){
        bool exp1 = this->state == rhs.state;
        //errs()<<"state comparison completed\n";
        if(this->state != rhs.state){
            return true;
        }
        if(this->state != Const){
            return false;
        }
        bool exp2 = dyn_cast<ConstantInt>(this->value) == dyn_cast<ConstantInt>(rhs.value);
        //errs()<<"value comparison completed\n";
        return !(exp1 && exp2);
        //return !(this->state == rhs.state && dyn_cast<ConstantInt>(this->value) == dyn_cast<ConstantInt>(rhs.value));
    }
    bool operator==(Const_& rhs){
        bool exp1 = this->state == rhs.state;
        //errs()<<"state comparison completed\n";
        if(this->state != rhs.state){
            return false;
        }
        if (this->state != Const){
            return true;
        }
        bool exp2 = dyn_cast<ConstantInt>(this->value) == dyn_cast<ConstantInt>(rhs.value);
        //errs()<<"value comparison completed\n";
        return (exp1 && exp2);
    }
} Const_;
typedef std::unordered_map<Value*, struct Const_> ConstPropContent;
typedef pair<unsigned, unsigned> Edge;

std::set<Value*> MPT;
std::unordered_map<Function*, std::set<GlobalVariable *>> MOD;

class ConstPropInfo : public Info {

	public:

        //typedef std::unordered_map<Value*, struct Const> ConstPropContent;


		ConstPropInfo() {}
        ConstPropContent infoMap;

        //constructor
		ConstPropInfo(ConstPropContent m) {
			infoMap = m;
		}

		void makeSet(ConstPropContent m ) {
            infoMap = m;
		}

        void setTop(Value* I){
            //errs()<<"reach set top\n";
            
            Const_ temp = {}; 
            temp.state = Top;
            temp.value = NULL;
            infoMap[I] = temp;
        }

        bool isConst (Value * I){
            if(infoMap.count(I)!=0 && infoMap[I].state == Const){
                return true;
            }else{
                return false;
            }
        }
        Constant * getConst (Value * I){
            if(isConst(I)){
                Constant * res = infoMap[I].value;
                return res;
            }
            errs()<<"something not right\n";
            return nullptr;
        }
        void setConst (Value * I, Constant* c){
            //errs()<<"reach set const\n";
            //errs()<< * I << *c << "\n";
            // if(!isa<GlobalVariable>(I)){
            //     return;
            // }
            Const_ temp = {};
            temp.state = Const;
            temp.value = c;
            infoMap[I] = temp;
            //errs()<<"Const_ temp not a problem\n";
        }
		void print() {
            for (auto ri = infoMap.begin(); ri != infoMap.end(); ++ri) {
                if(!isa<GlobalVariable>(ri->first)){
                    continue;
                }

				errs() << (*ri->first).getName()<<"=";

				if(ri->second.state == Top){
                    errs()<<"⊤";
                }else if(ri->second.state == Const){
                    errs()<<*(ri->second.value);
                }else if(ri->second.state == Bottom){
                    errs()<<"⊥";
                }
				errs() << "|";
			}
			errs() << "\n";
		}

		static bool equals(ConstPropInfo * info1, ConstPropInfo * info2) {
            if (info1->infoMap.size()!=info2->infoMap.size()) return false;
            //errs()<<"before equals for loop\n";
            for (auto it : info1->infoMap){
                Const_ c1=it.second;
                //errs()<<"accessing c1 completed\n";
                if(info2->infoMap.count(it.first)==0){
                    return false;
                }
                Const_ c2=info2->infoMap[it.first];
                //errs()<<"accessing c2 completed\n";
                if (c1 != c2){
                    return false;
                }
            }
            return true;
		}

		static ConstPropInfo* join(ConstPropInfo * info1, ConstPropInfo * info2, ConstPropInfo * result) {
            ConstPropContent resultMap;
            //errs()<<"%%%%%%%%%%%%%%%%%%%%%%%%%%%executing join \n";
            for (auto it : info1->infoMap){
                if(info2->infoMap.count(it.first)==0){
                    //info2 does not have this key
                    resultMap[it.first]=it.second;
                }else{
                    //info2 has this key
                    if(it.second.state == Top || info2->infoMap[it.first].state == Top){
                        //errs()<<"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% case 1 begins \n";
                        Const_ temp = {};
                        temp.state = Top;
                        temp.value = NULL;
                        resultMap[it.first] = temp;
                        //errs()<<"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% case 1 ends \n";
                    }else if(it.second.state == Bottom){
                        Const_ temp = {};
                        temp.state = info2->infoMap[it.first].state;
                        temp.value = info2->infoMap[it.first].value;
                        resultMap[it.first] = temp;
                    }else if(info2->infoMap[it.first].state == Bottom){
                        Const_ temp = {};
                        temp.state = it.second.state;
                        temp.value = it.second.value;
                        resultMap[it.first] = temp;
                    }else if(it.second.state == Const && info2->infoMap[it.first].state == Const){
                        if(it.second.value == info2->infoMap[it.first].value){
                            Const_ temp = {};
                            temp.state = Const;
                            temp.value = it.second.value;
                            resultMap[it.first] = temp;
                        }else{
                            Const_ temp = {};
                            temp.state = Top;
                            temp.value = NULL;
                            resultMap[it.first] = temp;                    
                        }
                    }
                }
            }

            for (auto it : info2->infoMap){
                if(info1->infoMap.count(it.first)==0){
                    //info1 does not have this key
                    resultMap[it.first]=it.second;
                }
                //if info1 has this key, then this key is already processed. Do nothing.
            }

            // for (auto it : info1->infoMap){
            //     if(info2->infoMap.count(it.first)==0){
            //         resultMap[it.first]=it.second;
            //     }else{
            //         if(it.second.state == Top || info2->infoMap[it.first].state == Top){
            //             errs()<<"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% case 1 begins \n";
            //             resultMap[it.first].state = Top;
            //             resultMap[it.first].value = NULL;
            //             errs()<<"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% case 1 ends \n";
            //         }else if(it.second.state == Bottom){
            //             resultMap[it.first].state = info2->infoMap[it.first].state;
            //             resultMap[it.first].value = info2->infoMap[it.first].value;
            //         }else if(info2->infoMap[it.first].state == Bottom){
            //             resultMap[it.first].state = it.second.state;
            //             resultMap[it.first].value = it.second.value;
            //         }else if(it.second.state == Const && info2->infoMap[it.first].state == Const){
            //             if(it.second.value == info2->infoMap[it.first].value){
            //                 resultMap[it.first].state = Const;
            //                 resultMap[it.first].value = it.second.value;
            //             }else{
            //                 resultMap[it.first].state = Top;
            //                 resultMap[it.first].value = NULL;                       
            //             }
            //         }
            //     }
            // }
            
            result->makeSet(resultMap);
            
            return result;
		}
};


namespace{
class ConstPropAnalysis : public DataFlowAnalysis<ConstPropInfo, true> {
	private:
		typedef pair<unsigned, unsigned> Edge;
		map<Edge, ConstPropInfo *> EdgeToInfo;

    
	public:
		ConstPropAnalysis(ConstPropInfo & bottom, ConstPropInfo & initialState) : 
			DataFlowAnalysis(bottom, initialState) {}

		void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									   std::vector<unsigned> & OutgoingEdges,
									   std::vector<ConstPropInfo *> & Infos) 
        {
            string instrName = I->getOpcodeName();
			unsigned instrIdx = InstrToIndex[I];
            std::map<Edge, ConstPropInfo *> edgeToInfo = getEdgeToInfo();
            ConstPropInfo * outInfo = new ConstPropInfo();
            ConstPropInfo * inInfo = new ConstPropInfo();
            //errs()<<"***************** entering flow function\n";
            //join all incoming info
            for (size_t i = 0; i < IncomingEdges.size(); i++) {
				Edge inEdge = make_pair(IncomingEdges[i], instrIdx);
				ConstPropInfo::join(outInfo, edgeToInfo[inEdge], outInfo);
                ConstPropInfo::join(inInfo, edgeToInfo[inEdge], inInfo);
			}
            if(I->isBinaryOp()){
                outInfo->setTop(I);
                Value * v0 = I->getOperand(0);
                Value * v1 = I->getOperand(1);
                //errs()<<"adding value 1:"<<*v0 << " and "<<*v1<<"\n";
                if((isa<Constant>(I->getOperand(0)) && isa<Constant>(I->getOperand(1)))){
                    auto temp = llvm::ConstantFolder();
                    outInfo->setConst(I, temp.CreateBinOp(((BinaryOperator *)(I))->getOpcode(),(Constant *) I->getOperand(0),(Constant *) I->getOperand(1)));
                }else if(inInfo->isConst(v0) && isa<Constant>(v1)){
                    auto temp = llvm::ConstantFolder();
                    Constant * v0_const = inInfo->getConst(v0);
                    outInfo->setConst(I,temp.CreateBinOp(((BinaryOperator *)(I))->getOpcode(),v0_const,(Constant *) v1));
                }else if(inInfo->isConst(v1) && isa<Constant>(v0)){
                    auto temp = llvm::ConstantFolder();
                    Constant * v1_const = inInfo->getConst(v1);
                    outInfo->setConst(I,temp.CreateBinOp(((BinaryOperator *)(I))->getOpcode(),v1_const,(Constant *) v0));
                }else if(inInfo->isConst(v0) && inInfo->isConst(v1)){
                    //errs()<<"adding to const from ininfo\n";
                    
                    auto temp = llvm::ConstantFolder();
                    Constant * v1_const = inInfo->getConst(v1);
                    Constant * v0_const = inInfo->getConst(v0);
                    Constant * c = temp.CreateBinOp(((BinaryOperator *)(I))->getOpcode(),v1_const,v0_const);
                    outInfo->setConst(I,c);

                    // errs()<<"added result: "<<*I<<"==" << *(temp.CreateBinOp(((BinaryOperator *)(I))->getOpcode(),v1_const,v0_const))<<"\n";
                    // errs()<<"is const "<< outInfo->isConst(I);
                    
                }

            }else if (I->isUnaryOp()){
                outInfo->setTop(I);
                Value * op0 = I->getOperand(0);
                if(isa<Constant>(I->getOperand(0))){
                    auto temp = llvm::ConstantFolder();
                    outInfo->setConst(I, temp.CreateUnOp(((UnaryOperator *)(I))->getOpcode(),(Constant *) I->getOperand(0)));
                }else if(inInfo->isConst(op0)){
                    auto temp = llvm::ConstantFolder();
                    outInfo->setConst(I, temp.CreateUnOp(((UnaryOperator *)(I))->getOpcode(),inInfo->getConst(op0)));
                }
            }else if (isa<LoadInst>(I)){
                LoadInst* linst = (LoadInst*)(I);
                Value * pt = linst->getPointerOperand();
                if (inInfo->isConst(pt)){
                    outInfo->setConst(I,inInfo->getConst(pt));
                }
                //problematic 
                // if(outInfo->infoMap.count(pt)){
                //     if(outInfo->infoMap[pt].state == Top){
                //         outInfo->setTop(I);
                //     }else if(outInfo->infoMap[pt].state == Const){
                //         outInfo->setConst(I, outInfo->infoMap[pt].value);
                //     }
                // }
            }else if(isa<StoreInst>(I)){

                StoreInst * sinst =(StoreInst *) (I);
                Value * ptrop = sinst->getPointerOperand();
                Value * valop = sinst->getValueOperand();
                // errs()<<"the value "<<*valop<<"\n";
                // errs()<<"const or not? "<<inInfo->isConst(valop)<<"\n";

                if(isa<Constant>(valop)){
                    //errs()<<"the value operand is const"<<*valop<<"\n";

                    Constant * c = (Constant *) valop;
                    //Value * v = ptrop;
                    outInfo->setConst(ptrop, c);
                }
                if(inInfo->isConst(valop)){
                        //errs()<<"the value operand is const in ininfo"<<*valop<<"\n";

                        //errs()<<"find a value operand constant "<< *valop <<"\n";
                        if(isa<Constant>(inInfo->getConst(valop))){
                            //errs()<<"the constant is here "<<*(inInfo->getConst(valop))<<"\n";
                            Constant * c = inInfo->getConst(valop);
                            outInfo->setConst(ptrop,c);
                        }

                    
                }
                // for(auto it : outInfo->infoMap){
                //     if (outInfo->isConst(it.first)){
                //         errs()<<"value after a store instruction: "<< *it.first <<"---";
                //         errs()<<*(outInfo->getConst(it.first))<<"\n";
                //     }else{
                //         errs()<<"value "<< *it.first <<"is not constant\n";
                //     }
                // }

            }else if (isa<CallInst>(I)){
                CallInst * cinst = (CallInst*)(I);
                for(unsigned j=0;j<cinst->getNumArgOperands();j++){
                    if(outInfo->infoMap.count((cinst->getArgOperand(j)))){
                        outInfo->setTop(cinst->getArgOperand(j));
                    }
                }
                Function * callee = cinst->getCalledFunction();
                for (auto gv : MOD[callee]){
                    outInfo->setTop(gv);
                }
            }else if( isa<ICmpInst>(I)){
                ICmpInst * icmpi = (ICmpInst *) (I);
                Value * op1 = I->getOperand(0);
                Value * op2 = I->getOperand(1);
                if(isa<Constant>(op1) && isa<Constant>(op2)){
                    auto temp = llvm::ConstantFolder();

                    outInfo->setConst(I, temp.CreateICmp(icmpi->getPredicate(), (Constant *) op1, (Constant *)op2));
                }else{
                    outInfo->setTop(I);
                }
            }else if(isa<FCmpInst>(I)){
                FCmpInst * fcmpi = (FCmpInst *) (I);
                Value * op1 = I->getOperand(0);
                Value * op2 = I->getOperand(1);
                if(isa<Constant>(op1) && isa<Constant>(op2)){
                    auto temp = llvm::ConstantFolder();
                    outInfo->setConst(I, temp.CreateFCmp( fcmpi->getPredicate(), (Constant *)op1, (Constant *) op2));
                }else{
                    outInfo->setTop(I);
                }
            }else if (isa<SelectInst>(I)){
                SelectInst * selinst = (SelectInst*) (I);
                if(isa<Constant>(selinst->getCondition()) && isa<Constant>(selinst->getTrueValue())&& isa<Constant>(selinst->getFalseValue())){
                    if(selinst->getCondition()){
                        outInfo->setConst(I, (Constant *)selinst->getTrueValue());
                    }else{
                        outInfo->setConst(I,(Constant *)selinst->getFalseValue());
                    }
                }else if(isa<Constant>(selinst->getTrueValue())&& isa<Constant>(selinst->getFalseValue())&& (isa<Constant>(selinst->getTrueValue())== isa<Constant>(selinst->getFalseValue()))){
                    outInfo->setConst(I,(Constant *) selinst->getTrueValue());
                }else{
                    outInfo->setTop(I);
                }
            }else if(isa<PHINode>(I)){
                
                unsigned ops = I->getNumOperands();
                Value * op0 = I->getOperand(0);
                Value * op1 = I->getOperand(1);
                if(inInfo->isConst(op0) && inInfo->isConst(op1)){
                    if (inInfo->infoMap[op0] == inInfo->infoMap[op1]){
                        outInfo->setConst(I,inInfo->getConst(op0));
                    }else{
                        outInfo->setTop(I);
                    }
                }else if(isa<Constant>(op0) && isa<Constant>(op1)){
                    if(op0 == op1){
                        outInfo->setConst(I, (Constant *)op0);
                    }else{
                        outInfo->setTop(I);
                    }
                }
                
                //bool flag = true;
                //unsigned op_num = I->getNumOperands();
                //
            }
            //errs()<<"outedge nums"<<OutgoingEdges.size()<<"\n";
            for (size_t i = 0; i < OutgoingEdges.size(); i++)
				Infos.push_back(outInfo);

            //errs()<<"***************** existing flow function\n";
        }
    
};


    struct ConstPropAnalysisPass : public CallGraphSCCPass {
        static char ID;
        // std::set<Value*> MPT;
        // std::unordered_map<Function*, std::set<GlobalVariable *>> MOD;
        std::set<GlobalVariable*> global_vals ;
        ConstPropAnalysisPass() : CallGraphSCCPass(ID) {}
        bool doInitialization(CallGraph &CG){
            Module * M = &(CG.getModule());
            for (auto &gv : M->getGlobalList()){
                global_vals.insert(&gv);
                if (gv.hasInitializer()){
                    Value * gpointed = (Value*) (gv.getInitializer());
                    MPT.insert(gpointed);
                }
            }
            for (Module::iterator F = M->begin(), FE = M->end(); F!=FE; ++F){
                for (Function::iterator B = F->begin(), BE= F->end();B!=BE; ++B){
                    for (BasicBlock::iterator Is = B->begin(),IsE = B->end();Is!=IsE;++Is){

                        Instruction * I = &*Is;
                        if(isa<StoreInst>(I)){
                            StoreInst * sinst = (StoreInst*) (I);
                            MPT.insert(sinst->getValueOperand());
                            //add every pointed to value to MPT
                        }else if(isa<CallInst>(I)){
                            CallInst * cinst = (CallInst*)(I);
                            for(unsigned j=0;j<cinst->getNumArgOperands();j++){
                                MPT.insert(cinst->getArgOperand(j));
                            }
                        }else if (isa<ReturnInst> (I)){
                            ReturnInst * retinst = (ReturnInst *) (I);
                            if(retinst->getReturnValue()!=NULL){
                                MPT.insert(retinst->getReturnValue());
                            }
                        }
                    }
                }
            }
            //LMOD
            for (Module::iterator Fs = M->begin(), FE = M->end(); Fs!=FE; ++Fs){
                Function * F = &*Fs;
                for (Function::iterator B = F->begin(), BE= F->end();B!=BE; ++B){
                    for (BasicBlock::iterator Is = B->begin(),IsE = B->end();Is!=IsE;++Is){
                        Instruction * I = &*Is;
                        if(isa<StoreInst>(I)){
                            StoreInst * sinst = (StoreInst*)(I);
                            if(isa<GlobalVariable>(sinst->getPointerOperand())){
                                if(MOD.count(F)){
                                    MOD[F].insert((GlobalVariable*)(sinst->getPointerOperand()));
                                }else{
                                    MOD[F] = std::set<GlobalVariable*>();
                                    MOD[F].insert((GlobalVariable*)(sinst->getPointerOperand()));
                                }
                            }else if(isa<GlobalVariable>(sinst->getValueOperand())){
                                if(MOD.count(F)){
                                    MOD[F].insert((GlobalVariable*)(sinst->getValueOperand()));
                                }else{
                                    MOD[F] = std::set<GlobalVariable*>();
                                    MOD[F].insert((GlobalVariable*)(sinst->getValueOperand()));
                                }
                            }
                        }
                        else if (isa<LoadInst>(I)){

                            auto Iscopy = Is;
                            Instruction * Inext = &*(++Iscopy);

                            if(isa<StoreInst>(Inext)){
                                for (auto val : MPT){
                                    if(isa<GlobalVariable>(val)){

                                        if(MOD.count(F)){
                                            MOD[F].insert((GlobalVariable*)(val));
                                        }else{
                                            MOD[F] = std::set<GlobalVariable*>();
                                            MOD[F].insert((GlobalVariable *)(val));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            /*for (auto v: MPT){
                errs()<< "hello: "<<*v <<"\n";
            }*/

            return false;

            //build MPT and LMOD data structure
        }
        bool runOnSCC(CallGraphSCC &SCC){

            for (CallGraphNode* callerNode : SCC){
                //not null
                if(Function* caller = callerNode->getFunction()){

                    if(MOD.count(caller)==0){
                        MOD[caller] = std::set<GlobalVariable*>();
                    }
                    for (auto pair: *callerNode){
                        CallGraphNode* calleeNode = pair.second;
                        //if callee not null
                        if(Function* callee = calleeNode->getFunction()){

                            if(MOD.count(callee)){
                                for (auto gv : MOD[callee]){
                                    MOD[caller].insert((GlobalVariable *)(gv));
                                }
                            }
                        }
                    }
                }
            }
            // for(auto it : MOD){
            //     errs()<<"CMOD: "<<it.first<< ": ";
            //     for (auto is : it.second){
            //         errs()<<*is<< " ";
            //     }
            //     errs()<<"\n";
            // }

            //build CMOD data structure
            return false;
        }
        bool doFinalization(CallGraph &CG){
            Module * M = &(CG.getModule());
            
            //errs()<<"after module \n";
            for (Module::iterator Fs = M->begin(), FE = M->end(); Fs!=FE; ++Fs){
    
                Function * F = &*Fs;
                //errs()<<"processing functions: "<< F<<"\n";
                ConstPropContent bott;
                ConstPropContent topm;
                for (auto gv : global_vals){
                    Const_ temp = {};
                    temp.state = Bottom; 
                    bott[gv] = temp;
                    Const_ temp2 = {};
                    temp2.state = Top;
                    temp2.value = NULL;
                    topm[gv] = temp2;
                }
                //errs()<<"processing functions after the for loop: "<< F<<"\n";
                ConstPropInfo bottom;
                bottom.makeSet(bott);
                ConstPropInfo initialState;
                initialState.makeSet(topm);
                ConstPropAnalysis * CPA = new ConstPropAnalysis(bottom, initialState);
                //errs()<<"calling worklist...: "<< F<<"\n";
                CPA->runWorklistAlgorithm(F);
                //errs()<<"finish calling work list...: "<< F<<"\n";
                CPA->print();
                //errs()<<"moving to the next function...current function: "<< F<<"\n";
            }
            
            // for(auto it : MOD){
            //     errs()<<"hello: "<<it.first<< ": ";
            //     for (auto is : it.second){
            //         errs()<<*is<< " ";
            //     }
            //     errs()<<"\n";
            // }
            return false;
        }
    }; 
}

char ConstPropAnalysisPass::ID = 0;
static RegisterPass<ConstPropAnalysisPass> X("cse231-constprop", "",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);