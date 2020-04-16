#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "231DFA.h"
#include <set>

using namespace llvm;
using namespace std;

class ReachingInfo : public Info {

	public:
		ReachingInfo() {}
        set<unsigned> infoSet;

        //constructor
		ReachingInfo(set<unsigned> s) {
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

		static bool equals(ReachingInfo * info1, ReachingInfo * info2) {
			return info1->infoSet == info2->infoSet;
		}

		static ReachingInfo* join(ReachingInfo * info1, ReachingInfo * info2, ReachingInfo * result) {
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


class ReachingDefinitionAnalysis : public DataFlowAnalysis<ReachingInfo, true> {
	private:
		typedef pair<unsigned, unsigned> Edge;
		map<Edge, ReachingInfo *> EdgeToInfo;
        set<string> firstCategory = {"alloca","load","select","icmp","fcmp","getelementptr"};
        set<string> secondCategory = {"br", "switch", "store"};
        set<string> thirdCategory = {"phi"};
	
	public:
		ReachingDefinitionAnalysis(ReachingInfo & bottom, ReachingInfo & initialState) : 
			DataFlowAnalysis(bottom, initialState) {}

		void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									   std::vector<unsigned> & OutgoingEdges,
									   std::vector<ReachingInfo *> & Infos) 
        {
			
			string instrName = I->getOpcodeName();
			unsigned instrIdx = InstrToIndex[I];
            std::map<Edge, ReachingInfo *> edgeToInfo = getEdgeToInfo();
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
			
			ReachingInfo * outInfo = new ReachingInfo();

			//join all incoming infos no matter the categor
			for (size_t i = 0; i < IncomingEdges.size(); i++) {
				Edge inEdge = make_pair(IncomingEdges[i], instrIdx);
				ReachingInfo::join(outInfo, edgeToInfo[inEdge], outInfo);
			}

			//join index category 1
			if (category == 1) {
				
                outInfo->infoSet.insert(instrIdx);
			}
            //join indices
			else if (category == 3) {
                BasicBlock* blk = I->getParent();
				Instruction * fNP = blk->getFirstNonPHI();
				unsigned fNPIdx = InstrToIndex[fNP];

				for (unsigned i = instrIdx; i < fNPIdx; i++) {
					outInfo->infoSet.insert(i);
				}
			}

			// Distribute result to outgoing edges
			for (size_t i = 0; i < OutgoingEdges.size(); i++)
				Infos.push_back(outInfo);
		}
};


namespace {
    struct ReachingDefinitionAnalysisPass : public FunctionPass {
        static char ID;
        ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            ReachingInfo bottom;
            ReachingInfo initialState;
            ReachingDefinitionAnalysis * RDA = new ReachingDefinitionAnalysis(bottom, initialState);
            RDA->runWorklistAlgorithm(&F);
            RDA->print();
            return false;
        }
    }; 
}  

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", "Do reaching definition on CFG",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);