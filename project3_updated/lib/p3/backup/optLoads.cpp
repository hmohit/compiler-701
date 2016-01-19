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
    optLoads() : FunctionPass(ID) {}
    llvm::DenseMap<llvm::Instruction*, int> map;
    //**********************************************************************
    // runOnFunction
    //**********************************************************************
    virtual bool runOnFunction(Function &F) {
    std::vector<llvm::Instruction*> killList;	//vector which keeps track of instructions to be removed

      //Create map
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
              addToMap(map, instrIter);
          }
      }
      isStore = 0;	// a flag which indicates the the previous instruction was a store
      Value *operand;	// a Value pointer which points to the value which needs to replace the emitted instruction in its use list
      Value *replacer;	// a Value pointer which points to the register which is being stored at (& loaded into)
       for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  for(BasicBlock::iterator instrIter = blockIter->begin(), instrEnd = blockIter->end(); instrIter != instrEnd; ++instrIter){
	      if(instrIter->getOpcode() == Instruction::Store && isStore == 0){    //store
                  isStore = 1;
                  operand = cast<Value>(&*instrIter->getOperand(0));
                  replacer = cast<Value>(&*instrIter->getOperand(1));
              }else if(instrIter->getOpcode() == Instruction::Store && isStore == 1){    //store following store
                  replacer = cast<Value>(&*instrIter->getOperand(1));
                  operand = cast<Value>(&*instrIter->getOperand(0));
              }else if(instrIter->getOpcode() == Instruction::Load && isStore == 1){    //load following store
                  isStore = 0;
                  if(cast<Value>(&*instrIter->getOperand(0))== replacer){
                      killList.push_back(instrIter);	// push load instruction onto vector 
                      llvm::Instruction& I = *instrIter;
	              I.replaceAllUsesWith(operand);	// replace the load instruction from its uses list
                      std::cerr << "%" << findKey(map, instrIter) << " is a useless load\n";
                 }
              }else 
                  isStore = 0;
          }
      }

      // iterate over the vector to remove instructions 
      if(!killList.empty()){
          for(std::vector<llvm::Instruction*>::iterator i = killList.begin(), killListe = killList.end(); i != killListe; ++i){
              llvm::Instruction *I = *i;
              I->eraseFromParent();
          }
          return true;	// since the function changes the opt
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
