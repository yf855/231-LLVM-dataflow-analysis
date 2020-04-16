#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "231DFA.h"
#include <set>

using namespace llvm;
using namespace std;

class LivenessInfo : public Info {

	public:
		LivenessInfo() {}
        set<unsigned> infoSet;

        //constructor
		LivenessInfo(set<unsigned> s) {
			infoSet = s;
		}

		void makeSet(set<unsigned> s) {
			infoSet = s;
		}

		void print() {
			for (auto temp : infoSet){
                errs() << temp << "|";
            }
            errs()<<"\n";
		}

		static bool equals(LivenessInfo * info1, LivenessInfo * info2) {
			return info1->infoSet == info2->infoSet;
		}

		static LivenessInfo* join(LivenessInfo * info1, LivenessInfo * info2, LivenessInfo * result) {
			set<unsigned> resultSet;
            for (auto it : info1->infoSet){
                resultSet.insert(it);
            }
            for (auto it: info2->infoSet){
                resultSet.insert(it);
            }
            result->makeSet(resultSet);
            
            return result;
		}
};


class LivenessAnalysis : public DataFlowAnalysis<LivenessInfo, false> {
	private:
		typedef pair<unsigned, unsigned> Edge;
		map<Edge, LivenessInfo *> EdgeToInfo;
        set<string> firstCategory = {"alloca","load","select","icmp","fcmp","getelementptr"};
        set<string> secondCategory = {"br", "switch", "store"};
        set<string> thirdCategory = {"phi"};
	
	public:
		LivenessAnalysis(LivenessInfo & bottom, LivenessInfo & initialState) : 
			DataFlowAnalysis(bottom, initialState) {}

		void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									   std::vector<unsigned> & OutgoingEdges,
									   std::vector<LivenessInfo *> & Infos) 
        {
			
			string instrName = I->getOpcodeName();
			unsigned instrIdx = InstrToIndex[I];
            std::map<Edge, LivenessInfo *> edgeToInfo = getEdgeToInfo();
			//identify category of this instruction
            unsigned category;
            //1st category
            if(I->isBinaryOp() || firstCategory.count(instrName)>0){
                category = 1;
            }
            //3rd category
            else if(thirdCategory.count(instrName)>0){
                category = 3;
            }
            else{
                category  =2;
            }

            //else{
                //errs()<<"impossible"<<"\n";
                //return;
            //}
			
			LivenessInfo * outInfo = new LivenessInfo();

			//join all incoming infos no matter the categor
			for (size_t i = 0; i < IncomingEdges.size(); i++) {
				Edge inEdge = make_pair(IncomingEdges[i], instrIdx);
				LivenessInfo::join(outInfo, edgeToInfo[inEdge], outInfo);
			}

            set<unsigned> operands;
            for (unsigned i=0;i< I->getNumOperands();i++){
                Instruction *opInstr = (Instruction *)(I->getOperand(i));
                if(InstrToIndex.count(opInstr)!=0){
                    operands.insert(InstrToIndex[opInstr]);
                }
            }

			//join index category 1
			if (category == 1 || category ==2) {
				
                //outInfo->infoSet.insert(instrIdx);
                LivenessInfo::join(outInfo,new LivenessInfo(operands),outInfo);
                if (category==1){
                    outInfo->infoSet.erase(instrIdx);
                }
                for (size_t i = 0; i < OutgoingEdges.size(); i++){
				    Infos.push_back(outInfo);
                }
			}
            //join indices
			else if (category == 3) {
                
                BasicBlock* blk = I->getParent();
				Instruction * fNP = blk->getFirstNonPHI();
				unsigned fNPIdx = InstrToIndex[fNP];

				for (unsigned i = instrIdx; i < fNPIdx; i++) {
					outInfo->infoSet.erase(i);
				}
                for (unsigned k =0 ;k<OutgoingEdges.size();k++){
                    set<unsigned> operand;
                    BasicBlock* k_parent = IndexToInstr[OutgoingEdges[k]]->getParent();
                    LivenessInfo *out_k = new LivenessInfo();
                    for(unsigned i = instrIdx;i<fNPIdx;i++){
                        //iterate through all phi nodes
                        Instruction *phiinstr = IndexToInstr[i];
                        for (unsigned j = 0;j<phiinstr->getNumOperands();j++){
                            //iterate through all operands in the instruction and use parent block as label
                            Instruction *oprandInstr = (Instruction *)(phiinstr->getOperand(j));
                            if(InstrToIndex.count(oprandInstr)!=0 && oprandInstr->getParent()==k_parent){
                                operand.insert(InstrToIndex[oprandInstr]);
                                break;
                            }
                        }
                    }
                    LivenessInfo::join(outInfo,new LivenessInfo(operand),out_k);
                    Infos.push_back(out_k);
                }
			}

			
		}
};


namespace {
    struct LivenessAnalysisPass : public FunctionPass {
        static char ID;
        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            LivenessInfo bottom;
            LivenessInfo initialState;
            LivenessAnalysis * RDA = new LivenessAnalysis(bottom, initialState);
            RDA->runWorklistAlgorithm(&F);
            RDA->print();
            return false;
        }
    }; 
}  

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", "Do Liveness on CFG",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);