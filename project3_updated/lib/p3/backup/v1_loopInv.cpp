//===--------------- printCode.cpp - Project 1 for CS 701 ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a skeleton of an implementation for the printCode
// pass of Univ. Wisconsin-Madison's CS 701 Project 1.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "liveVars"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/Support/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallSet.h"
#include <iostream>
#include <vector>
#include <stack>
#include <algorithm>
#include "instrMap.h"
#include "setControl.h"
#include "flags.h"

using namespace llvm;

STATISTIC(MovedLVInstructionCount, "Number of loop-invariant instructions moved.");

namespace {
  class loopInv : public FunctionPass {
    public:
    static char ID; // Pass identification, replacement for typeid
    loopInv() : FunctionPass(ID) {}
    llvm::DenseMap<llvm::Instruction*, int> map;

    //**********************************************************************
    // runOnFunction
    //**********************************************************************
    virtual bool runOnFunction(Function &F) {
      bool done = false;		//flag to check if another iteration is required
      bool changed = false;

      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> > DominatorMap;
      std::vector<std::set<llvm::BasicBlock*> > Dominators;
     
      std::set<llvm::BasicBlock*> allNodes; 
     
      std::stack<llvm::BasicBlock*> domWorkingSet;

      llvm::BasicBlock* root;		//keep track of the root block
      //create a map from instruction pointers to integers
      //create a set of all blocks in a function - used in dominator analysis
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  if(blockIter == F.begin()){
	  //the start node - add all its successors to the worklist
	      root = blockIter;
	      std::cerr << "The start node is: " << root << "\n";
	      succ_iterator basicSucc = succ_begin(blockIter);
 	      for(; basicSucc != succ_end(blockIter); ++basicSucc){
                  domWorkingSet.push(*basicSucc);
              }
	  }
	  allNodes.insert(blockIter);
	  //create map from instructions to integers -- REMOVE MAYBE
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              addToMap(map, instrIter);
          }
      }

      //add all nodes to dominator list for all nodes except root
      for(std::set<llvm::BasicBlock*>::iterator it = allNodes.begin(); it != allNodes.end(); ++it){
          if(*it != root){
	  //not the root node
	  DominatorMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(*it, allNodes));
          }else{
	  //add the root block to the root's dominator list
	  std::set<llvm::BasicBlock*> temp;
	  temp.insert(root);	  
	  DominatorMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(*it, temp));
          }
      }
/*
      //INITIAL DOMINATOR CHECK
      std::cerr << "The initial dominator lists: \n";
      for(std::set<llvm::BasicBlock*>::iterator it = allNodes.begin(); it != allNodes.end(); ++it){
          std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator i = DominatorMap.find(*it);  
	  std::cerr << "For block " << *it << " :";
	  std::set<llvm::BasicBlock*>::iterator j = (i->second).begin(); 
	  for(; j!= (i->second).end(); ++j)
	      std::cerr << *j << " ";
	  std::cerr << "\n";
      }

      //LIST OF ALL BLOCKS CHECK
      std::cerr << "The list of all blocks: \n";
      for(std::set<llvm::BasicBlock*>::iterator it = allNodes.begin(); it != allNodes.end(); ++it){
          std::cerr << *it << "\n";
      }
*/
/*      
      std::cerr << "\n" << "The first elements of the worklist are: \n";
      while(!domWorkingSet.empty()){
          std::cerr << domWorkingSet.top() << "\n";
	  domWorkingSet.pop();
      }  
*/

      //Dominator analysis
      //
      while(!domWorkingSet.empty()){
	 //read the element at the top of the worket 
         llvm::BasicBlock *curr = domWorkingSet.top();
	 //compute its dominators
         std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator itr = DominatorMap.find(curr);  
         std::set<llvm::BasicBlock*>::set &dom = (itr->second);		//dom points to current dominator set

//	 std::cerr << "Test\n";
//	 for(std::set<llvm::BasicBlock*>::iterator j = dom.begin(); j!= dom.end(); ++j){
//	      std::cerr << *j << " ";
//	 } 
// 	 std::cerr << "\n";

	 std::set<llvm::BasicBlock*> temp;// = allNodes;		//initialize to all nodes for 1st iteration
	 std::set<llvm::BasicBlock*> temp2;
	 pred_iterator pred = pred_begin(curr);
	 for(; pred != pred_end(curr); ++pred){
	     std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator predDom = DominatorMap.find(*pred); 
	     if(predDom != DominatorMap.end()){
	         setIntersection(temp, (predDom->second), temp2);
//	         temp = temp2; 
       	  std::cerr << "For block " << *pred << " :";
	  std::set<llvm::BasicBlock*>::iterator j = (predDom->second).begin(); 
	  for(; j!= (predDom->second).end(); ++j)
	      std::cerr << *j << " ";
	  std::cerr << "\n";
	         std::cerr << *pred << " iteration: ";
	         for(std::set<llvm::BasicBlock*>::iterator test = temp2.begin(); test != temp2.end(); ++test)
	             std::cerr << *test << " ";
	         std::cerr << "\n";
             } 
	 }
//	 std::cerr << curr << " Dominators are: ";
//	 for(std::set<llvm::BasicBlock*>::iterator test = temp.begin(); test != temp.end(); ++test)
//	     std::cerr << *test << " ";
//	 std::cerr << "\n";
	 domWorkingSet.pop();
      }
      //
      //Dominator analysis
/*
       //iterate through the blocks and create the genlist, killlist, liveafter and livebefore
      for(Function::iterator blockIter = F.end(), blockEnd = F.begin(); blockIter != blockEnd; ){
	  --blockIter;
	  std::set<llvm::Instruction*> tempKillList, temp, temp1;							//kill list
	  std::set<llvm::Instruction*> tempGenList;							//gen list
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              llvm::User::op_iterator operIter = instrIter->op_begin();					//iterate through the operands of an instr to generate the gen list
              for (; operIter != instrIter->op_end(); ++operIter){					//iterate through the operands to create the gen list
	          if(isa<Instruction>(operIter)){							//check if the operand is an instruction
		      if(tempKillList.find(cast<llvm::Instruction>(operIter)) == tempKillList.end())
		          tempGenList.insert(cast<llvm::Instruction>(operIter));  				//if not, add to the gen list
		  }   
              }
	      if(tempGenList.find(instrIter) == tempGenList.end())	
	          tempKillList.insert(instrIter);								//add instructions to kill list
	  }

	  //create a map from the block pointer to the vector index & insert in set
	  killMap.insert(std::pair<llvm::BasicBlock*, int>(blockIter, killList.size()));
	  killList.push_back(tempKillList);
	  genMap.insert(std::pair<llvm::BasicBlock*, int>(blockIter, genList.size()));
	  genList.push_back(tempGenList);

	  //create liveBefore and liveAfter sets for this block
	  std::set<llvm::Instruction*> tempLiveBefore;	
	  liveBeforeMap.insert(std::pair<llvm::BasicBlock*, int>(blockIter, liveBefore.size()));						
	  liveBefore.push_back(tempLiveBefore);

	  std::set<llvm::Instruction*> tempLiveAfter;							
	  liveAfterMap.insert(std::pair<llvm::BasicBlock*, int>(blockIter, liveAfter.size()));						
	  liveAfter.push_back(tempLiveAfter);

      }

      //populate the livebefore and liveafter sets
      while(done != true){
	  changed = false;
          for(Function::iterator blockIter = F.end(), blockEnd = F.begin(); blockIter != blockEnd; ){
	      --blockIter;
              std::map<llvm::BasicBlock*, int>::iterator gen = genMap.find(blockIter);
	      std::map<llvm::BasicBlock*, int>::iterator kill = killMap.find(blockIter);
              std::map<llvm::BasicBlock*, int>::iterator after = liveAfterMap.find(blockIter);
	      std::map<llvm::BasicBlock*, int>::iterator before = liveBeforeMap.find(blockIter);
	          std::set<llvm::Instruction *> temp, tempBefore;				//a temporary set to store the intermediate result
		  succ_iterator basicSucc = succ_begin(blockIter);
		  if(basicSucc == succ_end(blockIter)){						//no successor => the last block
		       setDifference(liveAfter[after->second], killList[kill->second], temp);	//compute temp = liveAfter - killList
		       setUnion(temp, genList[gen->second], tempBefore);	//compute liveBefore = temp U genList
		  }else{
		      std::set<llvm::Instruction*> tempAfter; 	
       	              succ_iterator basicSucc = succ_begin(blockIter);
		      for(; basicSucc != succ_end(blockIter); ++basicSucc){
	                  BasicBlock *succ = *basicSucc;		
	                  std::map<llvm::BasicBlock*, int>::iterator tempBefore = liveBeforeMap.find(succ);
		          tempAfter.insert(liveBefore[tempBefore->second].begin(), liveBefore[tempBefore->second].end());
	      	      }
		      //update the liveafter set
		      liveAfter[after->second].clear();
		      liveAfter[after->second].insert(tempAfter.begin(), tempAfter.end());
		
		      //update livebefore
		      setDifference(liveAfter[after->second], killList[kill->second], temp);	//compute temp = liveAfter - killList
		      setUnion(temp, genList[gen->second], tempBefore);				//compute liveBefore = temp U genList
		  }

		  if(tempBefore == liveBefore[before->second] && changed == false){
		          done = true;
		  }else{
                          done = false;
                          changed = true;
                  }		
		  liveBefore[before->second].clear();
                  liveBefore[before->second].insert(tempBefore.begin(), tempBefore.end());
          }	
      }
 
      //create livebefore and liveafter sets for instructions

      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
          // iterate over the instructions in a basic block 
          std::map<llvm::BasicBlock*, int>::iterator after = liveAfterMap.find(blockIter);
	  std::map<llvm::BasicBlock*, int>::iterator before = liveBeforeMap.find(blockIter);
	  for(BasicBlock::iterator instrIter = blockIter->end(), instrEnd = blockIter->begin(); instrIter != instrEnd;){
	      bool candidate = false;
              std::set <llvm::Instruction*> tempAfter;
              std::set <llvm::Instruction*> tempBefore;
      	      std::map<llvm::Instruction*, int>::iterator prev = instrBeforeMap.find(instrIter);
	      if(instrIter-- == blockIter->end()){
                  tempAfter = liveAfter[after->second];
	      }else{
		  tempAfter = instrBefore[prev->second];
              }
              llvm::User::op_iterator operIter = instrIter->op_begin();
              std::set <llvm::Instruction*> kill;
              std::set <llvm::Instruction*> gen, temp;
	      int code = instrIter->getOpcode();
	      if(instrIter->isCast() || instrIter->isBinaryOp() || instrIter->isShift() || code == 53 || code == 56 || code == 45 || code == 46 || code == 49 || code == 29 || code == 27 || code == 26)
	          candidate = true; 
              for (; operIter != instrIter->op_end(); ++operIter){
		  if(isa<Instruction>(operIter)){						//check if the operand is an instruction
		      if(kill.find(cast<llvm::Instruction>(operIter)) == kill.end())
		          gen.insert(cast<llvm::Instruction>(operIter));
		  }
	      }
	      if(gen.find(instrIter) == gen.end())
                  kill.insert(instrIter);
	      //compute liveafter and livebefore
	      setDifference(tempAfter, kill, temp);							//compute temp = liveAfter - killList
	      setUnion(temp, gen, tempBefore);								//compute liveBefore = temp U genList
	      instrBeforeMap.insert(std::pair<llvm::Instruction*, int>(instrIter, instrBefore.size()));						
	      instrBefore.push_back(tempBefore);

	      instrAfterMap.insert(std::pair<llvm::Instruction*, int>(instrIter, instrAfter.size()));						
	      instrAfter.push_back(tempAfter);
	      if(candidate && tempAfter.find(cast<llvm::Instruction>(instrIter)) == tempAfter.end()){
		  removeList.push_back(instrIter);
	      }
          }
      }  */

      return false; 
    }

    //**********************************************************************
    // print (do not change this method)
    //
    // If this pass is run with -f -analyze, this method will be called
    // after each call to runOnFunction.
    //**********************************************************************
    virtual void print(std::ostream &O, const Module *M) const {
        O << "This is loopInv.\n";
    }

    //**********************************************************************
    // getAnalysisUsage
    //**********************************************************************

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    };

  };
  char loopInv::ID = 0;

  // register the printCode class: 
  //  - give it a command-line argument (printCode)
  //  - a name ("print code")
  //  - a flag saying that we don't modify the CFG
  //  - a flag saying this is not an analysis pass
  RegisterPass<loopInv> X("loopInv", "Live vars analysis",
			   false, true);
}
