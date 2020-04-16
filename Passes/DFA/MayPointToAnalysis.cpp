#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "231DFA.h"
#include <map>
#include <set>
#include <string> 

using namespace llvm;
using namespace std;

class MayPointToInfo : public Info {

	public:
        // R is 1, M is 2
		MayPointToInfo() {}
        map<pair<unsigned,unsigned>,set<unsigned>> infoMap;

        //constructor
		MayPointToInfo(map<pair<unsigned,unsigned>,set<unsigned>> m) {
			infoMap = m;
		}

		void makeSet(map<pair<unsigned,unsigned>,set<unsigned>> m) {
			infoMap = m;
		}

		void print() {
			for (auto it : infoMap) {
				if (it.second.size() == 0)
					continue;
                if (it.first.first==1){
                    errs()<< "R" << it.first.second<<"->(";
                }else if (it.first.first == 2){
                    errs()<< "M" << it.first.second<<"->(";
                }
				for (auto sit : it.second) {
					errs() << "M" << sit << "/";
				}
				errs() << ")|";
			}
			errs() << "\n";
		}

		static bool equals(MayPointToInfo * info1, MayPointToInfo * info2) {
			if (info1->infoMap.size()!=info2->infoMap.size()) return false;
            for (auto it : info1->infoMap){
                if (it.second != info2->infoMap[it.first]){
                    return false;
                }
            }
            return true;
		}

		static MayPointToInfo* join(MayPointToInfo * info1, MayPointToInfo * info2, MayPointToInfo * result) {
			map<pair<unsigned,unsigned>,set<unsigned>> resultMap;
            for (auto it : info1->infoMap){
                for (auto m : it.second){
                    resultMap[it.first].insert(m);
                }
            }
            for (auto it : info2->infoMap){
                for (auto m : it.second){
                    resultMap[it.first].insert(m);
                }
            }
            result->makeSet(resultMap);
            
            return result;
		}
};


class MayPointToAnalysis : public DataFlowAnalysis<MayPointToInfo, true> {
	private:
		typedef pair<unsigned, unsigned> Edge;
		map<Edge, MayPointToInfo *> EdgeToInfo;

	
	public:
		MayPointToAnalysis(MayPointToInfo & bottom, MayPointToInfo & initialState) : 
			DataFlowAnalysis(bottom, initialState) {}

		void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									   std::vector<unsigned> & OutgoingEdges,
									   std::vector<MayPointToInfo *> & Infos) 
        {
			
			unsigned instrIdx = InstrToIndex[I];
            std::map<Edge, MayPointToInfo *> edgeToInfo = getEdgeToInfo();
			
			MayPointToInfo * outInfo = new MayPointToInfo();
            MayPointToInfo * inInfo = new MayPointToInfo();
			//join all incoming infos no matter the categor
			for (size_t i = 0; i < IncomingEdges.size(); i++) {
				Edge inEdge = make_pair(IncomingEdges[i], instrIdx);
				MayPointToInfo::join(outInfo, edgeToInfo[inEdge], outInfo);
                MayPointToInfo::join(inInfo, edgeToInfo[inEdge], inInfo);
			}

            if (isa<AllocaInst>(I)){
                pair<unsigned,unsigned> ridx = make_pair(1, instrIdx);
                outInfo->infoMap[ridx].insert(instrIdx);
            }else if(isa<BitCastInst>(I)){
                pair<unsigned,unsigned> ridx = make_pair(1,instrIdx);
                Instruction * I_op = (Instruction *) (I->getOperand(0));
                unsigned Rv = InstrToIndex[I_op];
                pair<unsigned,unsigned> rvidx = make_pair(1, Rv);
   
                for (auto mi : inInfo->infoMap[rvidx]){
                    outInfo->infoMap[ridx].insert(mi);
                }
            }else if(isa<GetElementPtrInst>(I)){
                pair<unsigned,unsigned> ridx = make_pair(1,instrIdx);
                GetElementPtrInst* pinst = (GetElementPtrInst*) (I);
                Instruction * I_op = (Instruction *)(pinst->getPointerOperand());
                unsigned Rv = InstrToIndex[I_op];
                pair<unsigned,unsigned> rvidx = make_pair(1, Rv);

                for (auto mi: inInfo->infoMap[rvidx]){
                    outInfo->infoMap[ridx].insert(mi);
                }
            }else if (isa<LoadInst>(I)){
                if(I->getType()->isPointerTy()){
                    pair<unsigned,unsigned>  ridx = make_pair(1,instrIdx);
                    LoadInst* linst = (LoadInst*)(I);
                    Instruction * I_op = (Instruction *)(linst->getPointerOperand());
                    unsigned Rp = InstrToIndex[I_op];
                    pair<unsigned,unsigned> rpidx =make_pair(1, Rp);
                    set<unsigned> X = inInfo->infoMap[rpidx];
                    for (auto it:X){
                        //for X-> Y of IN
                        pair<unsigned,unsigned> Mpx = make_pair(2,it);
                        //set<unsigned> Y;
                        for (auto j: inInfo->infoMap[Mpx]){
                            outInfo->infoMap[ridx].insert(j);
                        }
                    }
                    
                }

            }else if (isa<StoreInst>(I)){
                StoreInst * sinst = (StoreInst*) (I);
                Instruction * I_op = (Instruction *)(sinst->getValueOperand());
                unsigned rv = InstrToIndex[I_op];
                Instruction * I_opp = (Instruction *) (sinst->getPointerOperand());
                unsigned rp = InstrToIndex[I_opp];
                pair<unsigned,unsigned> rvidx = make_pair(1, rv);
                pair<unsigned,unsigned> rpidx = make_pair(1, rp);
                set<unsigned> X = inInfo->infoMap[rvidx];
                set<unsigned> Y = inInfo->infoMap[rpidx];

                for (auto y:Y){
                    pair<unsigned,unsigned> midx = make_pair(2 ,y);
                    for (auto x:X){
                        outInfo->infoMap[midx].insert(x);
                    }
                }
            }else if (isa<SelectInst>(I)){
                //join respectively
                pair<unsigned,unsigned> ridx = make_pair(1,instrIdx);
                SelectInst * selinst = (SelectInst*) (I);
                unsigned r1 = InstrToIndex[(Instruction *)(selinst->getTrueValue())];
                pair<unsigned,unsigned> r1idx = make_pair(1,r1);
                set<unsigned> X = inInfo->infoMap[r1idx];
                for (auto x : X){
                    outInfo->infoMap[ridx].insert(x);
                }
                unsigned r2 = InstrToIndex[(Instruction *)(selinst->getFalseValue())];
                pair<unsigned,unsigned> r2idx =make_pair(1,r2);
                X= inInfo->infoMap[r2idx];
                for (auto x:X){
                    outInfo->infoMap[ridx].insert(x);
                }
            }else if (isa<PHINode>(I)){
                //join respectively 
                BasicBlock* blk = I->getParent();
				Instruction * fNP = blk->getFirstNonPHI();
				unsigned fNPIdx = InstrToIndex[fNP];
                for (unsigned i = instrIdx; i < fNPIdx; i++) {
                    pair<unsigned,unsigned> ridx = make_pair(1,i);
                    Instruction *phiInstr = IndexToInstr[i];
					for (unsigned j=0;j<phiInstr->getNumOperands();j++){
                        unsigned Rj = InstrToIndex[(Instruction *)(phiInstr->getOperand(j))];
                        pair<unsigned,unsigned> Rjidx = make_pair(1,Rj);
                        set<unsigned> X = inInfo->infoMap[Rjidx];
                        for (auto x: X){
                            outInfo->infoMap[ridx].insert(x);
                        }
                    }
				}
            }
            
			for (size_t i = 0; i < OutgoingEdges.size(); i++)
				Infos.push_back(outInfo);
		}
};


namespace {
    struct MayPointToAnalysisPass : public FunctionPass {
        static char ID;
        MayPointToAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            MayPointToInfo bottom;
            MayPointToInfo initialState;
            MayPointToAnalysis * RDA = new MayPointToAnalysis(bottom, initialState);
            RDA->runWorklistAlgorithm(&F);
            RDA->print();
            return false;
        }
    }; 
}  

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", "",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);