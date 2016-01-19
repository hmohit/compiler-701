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
//
//Clint Lestourgeon
//
//Student ID: 906 984 9744
//
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
#include "flags.h"

#ifdef PRINTANALRESULTS
    static const bool PRINT_ANAL_RESULTS = true;
#else
    static const bool PRINT_ANAL_RESULTS = false;
#endif
#ifdef PRINTREMOVING
    static const bool PRINT_REMOVING = true;
#else
    static const bool PRINT_REMOVING = false;
#endif

using namespace llvm;

STATISTIC(RemovedInstructionCount, "Number of useless assignments found.");

namespace {
  class liveVars : public FunctionPass {
    public:
    static char ID; // Pass identification, replacement for typeid
    liveVars() : FunctionPass(ID) {}
    llvm::DenseMap<llvm::Instruction*, int> map;
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
      std::vector<std::set<llvm::Instruction*> > liveBefore;
      std::vector<std::set<llvm::Instruction*> > liveAfter;
      std::vector<std::set<llvm::Instruction*> > killList;
      std::vector<std::set<llvm::Instruction*> > genList;

      std::map<llvm::Instruction*, int> instrBeforeMap;
      std::map<llvm::Instruction*, int> instrAfterMap;
      std::vector<std::set<llvm::Instruction*> > instrBefore;   
      std::vector<std::set<llvm::Instruction*> > instrAfter;   

      std::vector<llvm::Instruction*> removeList;	//a list to keep track of useless loads

      //create a map from instruction pointers to integers
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              addToMap(map, instrIter);
          }
      }

       //iterate through the blocks and create the genlist, killlist, liveafter and livebefore
      for(Function::iterator blockIter = F.end(), blockEnd = F.begin(); blockIter != blockEnd; ){
	  --blockIter;
	  std::set<llvm::Instruction*> tempKillList, temp, temp1;						//kill list
	  std::set<llvm::Instruction*> tempGenList;								//gen list
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              llvm::User::op_iterator operIter = instrIter->op_begin();						//iterate through the operands of an instr to generate the gen list
              for (; operIter != instrIter->op_end(); ++operIter){						//iterate through the operands to create the gen list
	          if(isa<Instruction>(operIter)){								//check if the operand is an instruction
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
		       setUnion(temp, genList[gen->second], tempBefore);			//compute liveBefore = temp U genList
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
      }

      if(PRINT_ANAL_RESULTS){
          std::cerr << "\nFUNCTION " << F.getName().str() << "\n";
          for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
              std::map<llvm::BasicBlock*, int>::iterator after = liveAfterMap.find(blockIter);
	      std::map<llvm::BasicBlock*, int>::iterator before = liveBeforeMap.find(blockIter);
              std::cerr << "\nBASIC BLOCK " << blockIter->getName().str() << " ";
	      std::cerr << "L-Before: {";
	      printSet(liveBefore[before->second], map);
  	      std::cerr << " }\tL-After: {";
	      printSet(liveAfter[after->second], map);
	      std::cerr << " }\n";    
	      for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
                  std::map<llvm::Instruction*, int>::iterator instrAft = instrAfterMap.find(instrIter);
	          std::map<llvm::Instruction*, int>::iterator instrBef = instrBeforeMap.find(instrIter);
                  std::cerr << "%" << findKey(map, instrIter) << ":\t";
	          std::cerr << "L-Before: {";
	          printSet(instrBefore[instrBef->second], map);
	          std::cerr << " }\tL-After: {";
	          printSet(instrAfter[instrAft->second], map);
	          std::cerr << " }\n";    
              }
          }
      }

      std::vector<llvm::Instruction*>::iterator rItr = removeList.begin();
      for(; rItr != removeList.end(); ++rItr){
          llvm::Instruction *I = *rItr;
          if(PRINT_REMOVING) 
              std::cerr << "removing useless assignment %" << findKey(map, *rItr) << "\n";
	  I->eraseFromParent(); 
	  RemovedInstructionCount++;
      }
      if(removeList.empty())
          return false;  // because we have NOT changed this function
      return true;
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
