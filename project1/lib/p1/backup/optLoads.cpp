//===--------------- optLoads.cpp - Project 1 for CS 701 ---------------===//
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

#define DEBUG_TYPE "optLoads"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include <iostream>
#include <vector>
#include "instrMap.h"
using namespace llvm;

namespace {
  class optLoads : public FunctionPass {
    public:
    static char ID; // Pass identification, replacement for typeid
    int isStore;
    int killCount;
    std::vector<llvm::Instruction*> killList;
    optLoads() : FunctionPass(ID) {}
    llvm::DenseMap<llvm::Instruction*, int> map;
    //**********************************************************************
    // runOnFunction
    //**********************************************************************
    virtual bool runOnFunction(Function &F) {
      // print fn name
      // MISSING: Add code here to do the following:
      //          1. Iterate over the instructions in F, creating a
      //             map from instruction address to unique integer.
      //             (It is probably a good idea to put this code in
      //             a separate, private method.)
      //          2. Iterate over the basic blocks in the function and
      //             print each instruction in that block using the format
      //             given in the assignment.

      //Create map
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              addToMap(map, instrIter);
          }
      }
      isStore = 0;
      killCount = 0;
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              std::cerr << "%" << findKey(map, instrIter) << ":" << "\t"; 
	      std::cerr << instrIter->getOpcodeName(instrIter->getOpcode()) << "\t";
              if(strcmp((instrIter->getOpcodeName(instrIter->getOpcode())), "store") == 0){
                  std::cerr << "& is a store.\n";
                  isStore = 1;
              }else
                  isStore = 0;
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
              if(operIter == instrIter->op_end() && isStore == 1){
                  std::cerr << "Optimization is possible\n";
                  killList.push_back(instrIter);
              }
          }
          std::cerr << "\n";
      }
      printMap(map);
      for(std::vector<llvm::Instruction*>::iterator i = killList.begin(); i != killList.end(); ++i){
          std::cerr << "%" << findKey(map, *i) << "\n";
      }
      return false;  // because we have NOT changed this function
    }

    //**********************************************************************
    // print (do not change this method)
    //
    // If this pass is run with -f -analyze, this method will be called
    // after each call to runOnFunction.
    //**********************************************************************
    virtual void print(std::ostream &O, const Module *M) const {
        O << "This is optLoads.\n";
    }

    //**********************************************************************
    // getAnalysisUsage
    //**********************************************************************

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
    };

  };
  char optLoads::ID = 0;

  // register the printCode class: 
  //  - give it a command-line argument (printCode)
  //  - a name ("print code")
  //  - a flag saying that we don't modify the CFG
  //  - a flag saying this is not an analysis pass
  RegisterPass<optLoads> X("optLoads", "optimize unnecessary loads",
			   false, false);
}
