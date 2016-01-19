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
#include <algorithm>
#include "instrMap.h"
#include "setControl.h"
using namespace llvm;

namespace {
  class liveVars : public FunctionPass {
    public:
    static char ID; // Pass identification, replacement for typeid
    liveVars() : FunctionPass(ID) {}
    llvm::DenseMap<llvm::Instruction*, int> map;
/*    std::map<llvm::BasicBlock*, int> liveBeforeMap;
    std::map<llvm::BasicBlock*, int> liveAfterMap;
    std::map<llvm::BasicBlock*, int> killMap;
    std::map<llvm::BasicBlock*, int> genMap;
    
    std::vector<std::set<llvm::Instruction*> > liveBefore;
    std::vector<std::set<llvm::Instruction*> > liveAfter;
    std::vector<std::set<llvm::Instruction*> > killList;
    std::vector<std::set<llvm::Instruction*> > genList;*/
    //**********************************************************************
    // runOnFunction
    //**********************************************************************
    virtual bool runOnFunction(Function &F) {
      bool done = false;		//flag to check if another iteration is required
      bool changed = false;
      std::map<llvm::BasicBlock*, int> liveBeforeMap;
      std::map<llvm::BasicBlock*, int> liveAfterMap;
      std::map<llvm::BasicBlock*, int> killMap;
      std::map<llvm::BasicBlock*, int> genMap;
      std::map<llvm::Instruction*, int> instrBeforeMap;

      std::map<llvm::Instruction*, int> instrAfterMap;
      std::map<llvm::Instruction*, int> intsrBeforeMap;
      std::vector<std::set<llvm::Instruction*> > instrBefore;   
      std::vector<std::set<llvm::Instruction*> > instrAfter;   

      std::vector<std::set<llvm::Instruction*> > liveBefore;
      std::vector<std::set<llvm::Instruction*> > liveAfter;
      std::vector<std::set<llvm::Instruction*> > killList;
      std::vector<std::set<llvm::Instruction*> > genList;
      //iterate through the blocks and create the genlist, killlist, liveafter and livebefore
      for(Function::iterator blockIter = F.end(), blockEnd = F.begin(); blockIter != blockEnd; ){
	  --blockIter;
	  std::set<llvm::Instruction*> tempKillList;							//kill list
	  std::set<llvm::Instruction*> tempGenList;							//gen list
	  std::cerr << "\nBlock " << blockIter << "\n";
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
	      addToMap(map, instrIter);
              tempKillList.insert(instrIter);								//add instructions to kill list
              llvm::User::op_iterator operIter = instrIter->op_begin();					//iterate through the operands of an instr to generate the gen list
              for (; operIter != instrIter->op_end(); ++operIter){					//iterate through the operands to create the gen list
	          if(isa<Instruction>(operIter)){							//check if the operand is an instruction
		      if(tempKillList.find(cast<llvm::Instruction>(operIter)) == tempKillList.end()){		//check if defined in this block
		          tempGenList.insert(cast<llvm::Instruction>(operIter));  				//if not, add to the gen list
		      }			       	
		  }   
              }
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

/*
          std::map<llvm::BasicBlock*, int>::iterator it = killMap.find(blockIter);
	  if(it != killMap.end()){ 
              for(std::set<llvm::Instruction*>::iterator itr = killList[it->second].begin(); itr != killList[it->second].end(); ++itr){
	          std::cerr << *itr << "\t";
	      }
	  }
	  std::cerr << "\n";
          std::map<llvm::BasicBlock*, int>::iterator i = genMap.find(blockIter);
	  if(i != genMap.end()){ 
              for(std::set<llvm::Instruction*>::iterator itr = genList[i->second].begin(); itr != genList[i->second].end(); ++itr){
	          std::cerr << *itr << "\t";
	      }
	  }
*/
	  // with the kill list and genlist generated, start working on the live before and live after sets
	  std::cerr << "Kill List:\n";
	  for(std::set<llvm::Instruction*>::iterator it = tempKillList.begin(); it != tempKillList.end(); ++it){
	      std::cerr << *it << "\n";
	  } 
	  std::cerr << "Gen List:\n";
	  for(std::set<llvm::Instruction*>::iterator it = tempGenList.begin(); it != tempGenList.end(); ++it){
	      std::cerr << *it << "\n";
	  }      
	  std::cerr << "The basic block " << blockIter << "s successors are: \n";
	  for(succ_iterator basicSucc = succ_begin(blockIter); basicSucc != succ_end(blockIter); ++basicSucc){
	      BasicBlock *succ = *basicSucc;		
	      std::cerr << succ << "\t";
	  }
	  std::cerr << "\n";
      }
      std::cerr << "Completed the first part.\n";
      //create the livebefore and liveafter sets
      while(done != true){
	  changed = false;
	  std::cerr << "\n\nNEW RUN\n";
          for(Function::iterator blockIter = F.end(), blockEnd = F.begin(); blockIter != blockEnd; ){
	      --blockIter;
              std::map<llvm::BasicBlock*, int>::iterator gen = genMap.find(blockIter);
	      std::map<llvm::BasicBlock*, int>::iterator kill = killMap.find(blockIter);
              std::map<llvm::BasicBlock*, int>::iterator after = liveAfterMap.find(blockIter);
	      std::map<llvm::BasicBlock*, int>::iterator before = liveBeforeMap.find(blockIter);
//	      if(iter != liveAfterMap.end()){		// check if live after exists for current block 
		  succ_iterator basicSucc = succ_begin(blockIter);
		  if(basicSucc == succ_end(blockIter)){		//no successor => the last block
		       std::set<llvm::Instruction *> temp;	//a temporary set to store the intermediate result
		       setDifference(liveAfter[after->second], killList[kill->second], temp);	//compute temp = liveAfter - killList
		       setUnion(temp, genList[gen->second], liveBefore[before->second]);	//compute liveBefore = temp U genList
		       std::cerr << "Livebefore for block " << blockIter << ": ";
		       printSet(liveBefore[before->second]);
		       std::cerr << "\n";
		  }else{
		      std::set<llvm::Instruction*> tempAfter; 	
       	              for(; basicSucc != succ_end(blockIter); ++basicSucc){
	                  BasicBlock *succ = *basicSucc;		
	                  std::map<llvm::BasicBlock*, int>::iterator tempBefore = liveBeforeMap.find(succ);
		          tempAfter.insert(liveBefore[tempBefore->second].begin(), liveBefore[tempBefore->second].end());
                          std::cerr << succ << "\t";
	      	      }
	              std::cerr << "\n";
//		      std::cerr << "liveafter for block " << blockIter << ": ";
//		      printSet(tempAfter);
		      //updtare the liveafter set
		      liveAfter[after->second].clear();
		      liveAfter[after->second].insert(tempAfter.begin(), tempAfter.end());
		      std::cerr << "updated liveafter for block " << blockIter << ": ";
		      printSet(liveAfter[after->second]);
		
		      //update livebefore
		      std::set<llvm::Instruction *> temp;	//a temporary set to store the intermediate result
		      setDifference(liveAfter[after->second], killList[kill->second], temp);	//compute temp = liveAfter - killList
		      setUnion(temp, genList[gen->second], liveBefore[before->second]);	//compute liveBefore = temp U genList
		      std::cerr << "Livebefore for block " << blockIter << ": ";
		      printSet(liveBefore[before->second]);
		      std::cerr << "\n";
		
		      //check if iteration required
		      pred_iterator basicPred = pred_begin(blockIter);
		      if(basicPred != pred_end(blockIter)){		//except the first block
		          for(; basicPred != pred_end(blockIter); ++basicPred){
	                      BasicBlock *pred = *basicPred;	
//			      std::cerr << pred << "\n";	
	                      std::map<llvm::BasicBlock*, int>::iterator tempAfter = liveAfterMap.find(pred);
			      if(liveBefore[before->second] == liveAfter[tempAfter->second] && changed == false){
//			          std::cerr << "Livebefore matches new one\n";
				  done = true;
			      }else{
//				  std::cerr << "Livebefore does not match new one\n";
				  done = false;
			          changed = true;
		              }
	      	          }
    
		      }
		  }
//	      }
          }	
      }
 
      //create livebefore and liveafter sets for instructions
      //

      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
          // iterate over the instructions in a basic block 
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              llvm::User::op_iterator operIter = instrIter->op_end();
              std::set <llvm::Instruction*> kill;
              std::set <llvm::Instruction*> gen;
              kill.insert(instrIter);
              for (; operIter != instrIter->op_begin(); --operIter){
		  if(isa<Instruction>(operIter)){	//check if the operand is an instruction
		      if(kill.find(cast<llvm::Instruction>(operIter)) == kill.end())
		          gen.insert(cast<llvm::Instruction>(operIter));
		  }
	      }
          }
      }
 
      //create livebefore and liveafter sets for instructions 
/*      int i = 0;
      for(std::vector<std::set<llvm::Instruction*> >::iterator it = killList.begin(); it != killList.end(); ++it){
           for(std::set<llvm::Instruction*>::iterator itr = killList[i].begin(); itr != killList[i].end(); ++itr){
	      std::cerr << *itr << "\t";
	  }
	  i++; 
	  std::cerr << "\n";
     }*/

      //print
/*      std::cerr << "\nFUNCTION " << F.getName().str() << "\n";
      // iterate over the blocks in a function
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
          std::cerr << "\nBASIC BLOCK " << blockIter->getName().str() << "\n";
          // iterate over the instructions in a basic block 
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              std::cerr << "%" << findKey(map, instrIter) << ":" << "\t"; 
	      std::cerr << instrIter->getOpcodeName(instrIter->getOpcode()) << "\t";
              llvm::User::op_iterator operIter = instrIter->op_begin();
              for (; operIter != instrIter->op_end(); ++operIter){
		  if(!isa<Instruction>(operIter)){
			if (cast<Value>(operIter)->hasName())
				std::cerr << (cast<Value>(operIter)->getName()).data() << "\t";
			else
				std::cerr << "XXX" << "\t";
		  }else{
                      std::cerr << "%" << findKey(map, cast<llvm::Instruction>(operIter)) << "\t";         
                  }
	      }
		std::cerr << "\n";
          }
      }*/
      return false;  // because we have NOT changed this function
    }

    //**********************************************************************
    // print (do not change this method)
    //
    // If this pass is run with -f -analyze, this method will be called
    // after each call to runOnFunction.
    //**********************************************************************
    virtual void print(std::ostream &O, const Module *M) const {
        O << "This is liveVars.\n";
    }

    //**********************************************************************
    // getAnalysisUsage
    //**********************************************************************

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
    };

  };
  char liveVars::ID = 0;

  // register the printCode class: 
  //  - give it a command-line argument (printCode)
  //  - a name ("print code")
  //  - a flag saying that we don't modify the CFG
  //  - a flag saying this is not an analysis pass
  RegisterPass<liveVars> X("liveVars", "Live vars analysis",
			   false, true);
}
