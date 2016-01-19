//===--------------- printCode.cpp - Project 1 for CS 701 ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// An implementation for the loop-invariant code motion
// pass of Univ. Wisconsin-Madison's CS 701 Project 3.
//
// Clint Lestourgeon
// Student ID: 906 984 9744
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "loopInv"
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
#include "naturalLoop.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#ifdef PRINTDOM 
    static const bool PRINT_DOM = true;
#else
    static const bool PRINT_DOM = false;
#endif
#ifdef PRINTMERGE
    static const bool PRINT_MERGE = true;
#else
    static const bool PRINT_MERGE = false;
#endif
#ifdef PRINTLOOPS
    static const bool PRINT_LOOPS = true;
#else
    static const bool PRINT_LOOPS = false;
#endif
#ifdef PRINTPRE
    static const bool PRINT_PRE = true;
#else
    static const bool PRINT_PRE = false;
#endif
#ifdef PRINTMOVING
    static const bool PRINT_MOVING = true;
#else
    static const bool PRINT_MOVING = false;
#endif

using namespace llvm;

STATISTIC(MovedLVInstructionCount, "Number of loop-invariant instructions moved.");

bool cmpFunction(naturalLoop a, naturalLoop b){
    if(a.loop.size() != b.loop.size())
        return a.loop.size() > b.loop.size();
    else
	return a.header->getName().str() > b.header->getName().str(); 
}

bool cmp(llvm::BasicBlock *a, llvm::BasicBlock *b){
    return a->getName().str() < b->getName().str();
}

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

      //data structures for dominators
      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> > DominatorMap;
     
      //set of all BBs in a function
      std::set<llvm::BasicBlock*> allNodes; 
    
      //work set for the dominator analysis
      std::stack<llvm::BasicBlock*> domWorkingSet;

      //work set for detecting backedges
      std::stack<llvm::BasicBlock*> workSet;

      //keep track of visited nodes in DFS
      std::vector<llvm::BasicBlock*> visited;		

      //map headers to nodes with backedges to it
      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> > headerMap;
 
      //keep track of the root block
      llvm::BasicBlock* root;		   
    
      //a vector of all natural loops in a function
      std::vector<naturalLoop> nLoops;

      //a vector of definitions in the loop body
      std::vector<llvm::Instruction*> useList;

 
      //create a map from instruction pointers to integers
      //create a set of all blocks in a function - used in dominator analysis
      for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
	  if(blockIter == F.begin()){
	      //the start node - add all its successors to the worklist
	      root = blockIter;

	      //add the root to the working set, push it's successors back on when popped
	      domWorkingSet.push(root);

	      //add the root node to its dominator list
	      std::set<llvm::BasicBlock*> temp;
	      temp.insert(root);	  
	      DominatorMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(root, temp));

	      //initialize the working set with the root node's successors
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


      //add all nodes to dominator list for all reachable nodes except the root
      while(!domWorkingSet.empty()){
	  llvm::BasicBlock *it = domWorkingSet.top();
          if(it != root){
	      //not the root node
	      domWorkingSet.pop();
              std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator currDom = DominatorMap.find(it);
	      if(currDom == DominatorMap.end()){  
		  //hasn't been visited before
	          DominatorMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(it, allNodes));
	      
                  //add the node's successors to the work list
	          succ_iterator basicSucc = succ_begin(it);
 	          for(; basicSucc != succ_end(it); ++basicSucc){
                      domWorkingSet.push(*basicSucc);
		      workSet.push(*basicSucc);
                  }
	      }
          }else{
	      //initialize the working set with the root node's successors & exit
	      domWorkingSet.pop();
	      succ_iterator basicSucc = succ_begin(it);
 	      for(; basicSucc != succ_end(it); ++basicSucc){
                  domWorkingSet.push(*basicSucc);
              }
	      break;
          }
      }

 
      //Dominator analysis
      while(!domWorkingSet.empty()){
	 //read the element at the top of the worket 
         llvm::BasicBlock *curr = domWorkingSet.top();
         std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator currDom = DominatorMap.find(curr);  
	 //compute its dominators
         std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator itr = DominatorMap.find(curr);  
	 std::set<llvm::BasicBlock*> temp = allNodes;		//initialize to all nodes for 1st iteration
	 std::set<llvm::BasicBlock*> temp2;
	 pred_iterator pred = pred_begin(curr);
	 for(; pred != pred_end(curr); ++pred){
	     std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator predDom = DominatorMap.find(*pred); 
	     //predDom->second is the dominator set for block predDom
	     setIntersection(temp, (predDom->second), temp2);
	     temp = temp2;
	     temp2.clear();
	 }
	 temp.insert(curr);
	 domWorkingSet.pop();

	 if(temp != (currDom->second)){
	     (currDom->second).clear();
	     (currDom->second).insert(temp.begin(), temp.end());
	     succ_iterator basicSucc = succ_begin(curr);
 	     for(; basicSucc != succ_end(curr); ++basicSucc){
                 domWorkingSet.push(*basicSucc);
	     }
	 }
      }

      if(PRINT_DOM){
          std::cerr << "\nFUNCTION " << F.getName().str() << "\n";
          // iterate over the blocks in a function
          for(Function::iterator blockIter = F.begin(), blockEnd = F.end(); blockIter != blockEnd; ++blockIter){
              std::cerr << "BASIC BLOCK " << blockIter->getName().str() << "  ";
              // iterate over the instructions in a basic block 
	      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator currDom = DominatorMap.find(blockIter);
 	      std::vector<llvm::BasicBlock*> temp;
	      if(currDom == DominatorMap.end()){
	          std::cerr << "DOM-Before:"<< "  { }\t" << "  DOM-After:" << " { }\n";
	      }else{
		  std::set<llvm::BasicBlock*>::iterator dom = (currDom->second).begin();
		  for(; dom != (currDom->second).end(); ++dom)
		      temp.push_back(*dom);
		  std::sort(temp.begin(), temp.end(), cmp);
		  std::cerr << "DOM-Before: { ";
		  std::vector<llvm::BasicBlock*>::iterator i = temp.begin();
		  for(; i!= temp.end(); ++i){
		      llvm::BasicBlock *nuc = *i;
		      if(nuc != blockIter)
		          std::cerr << (*i)->getName().str() << " ";
		  }
		  std::cerr << "}  DOM-After: { ";
		  i = temp.begin();
		  for(; i!= temp.end(); ++i){
		      std::cerr << (*i)->getName().str() << " ";
		  }
		  std::cerr << "}\n";
	      }
          }
      }      


      //backedge detection 
      while(!workSet.empty()){
          llvm::BasicBlock *BB = workSet.top();		//the current BB being analyzed
	  if(std::find(visited.begin(), visited.end(), BB) == visited.end()){		//block hasn't been visited before
	      //the dominator set for BB
	      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator BBDom = DominatorMap.find(BB);	 
	      std::set<llvm::BasicBlock*> dom = BBDom->second;

	      //mark node as visited & pop from stack
	      visited.push_back(BB);
	      workSet.pop();

	      //iterate over the successors to find backedges
 	      succ_iterator basicSucc = succ_begin(BB);
 	      for(; basicSucc != succ_end(BB); ++basicSucc){
                  if(dom.count(*basicSucc) ){
		      //a backedge is found
		      //check if the header has pre-existing backedges
		      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator it = headerMap.find(*basicSucc);
		      if(it == headerMap.end()){
		          //a new header is detected, add the node to the map
			  std::set<llvm::BasicBlock*> temp;
			  temp.insert(BB);
		          headerMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(*basicSucc, temp));
		      }else{
			  //the header has pre-existing backedges
			  (it->second).insert(BB);
		      }
	          }else{
	              if(std::find(visited.begin(), visited.end(), *basicSucc) == visited.end())	//do not push succesor if backedge found
		          workSet.push(*basicSucc);	
	          }	      
	      }
	  }else
	      workSet.pop();		//if visited, pop from stack
      }
	
	
      //detect all natural loops
      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator it = headerMap.begin();
      //iterate over all headers identified in previous step
      for(; it != headerMap.end(); ++it){
	  //header is the head node
          llvm::BasicBlock *header = it->first;
          std::set<llvm::BasicBlock*> tempLoop;
 	  //iterate over all the nodes that have backedges to determine natural loops
	  std::set<llvm::BasicBlock*>::iterator list = (it->second).begin();
	  for(; list != (it->second).end(); ++list){
	      llvm::BasicBlock *node = *list;
	      //create a temp set and add the header to the set
	      tempLoop.insert(header);
	      //push node onto stack
	      workSet.push(node);
	      while(!workSet.empty()){
		  llvm::BasicBlock *nuc = workSet.top();	//node under consideration
		  workSet.pop();				//pop from top of stack
	          if(tempLoop.find(nuc) == tempLoop.end()){
		      //node not in body, add it in
		      tempLoop.insert(nuc);
		      //add all the node's predecessors to the stack
		      pred_iterator pred = pred_begin(nuc);
	  	      for(; pred != pred_end(nuc); ++pred){
			  if(tempLoop.find(*pred) == tempLoop.end())
      		              workSet.push(*pred);	
		      }
		  }
	      }	
	      //the loop body should now be contained in tempLoop
          }
	  //store the header and its loop
	  naturalLoop insertLoop(header, tempLoop);
	  nLoops.push_back(insertLoop);
	  if(PRINT_MERGE){
	      if((it->second).size() > 1)
	          std::cerr << "merging " << (it->second).size() << " loops with header " << header->getName().str() << "\n";
	  }
      }


      //sort the natural loops
      std::sort(nLoops.begin(), nLoops.end(), cmpFunction);

      if(PRINT_LOOPS){
         std::cerr << "FUNCTION " << F.getName().str() <<"\n" << "LOOPS\n";
         std::vector<naturalLoop>::iterator nl = nLoops.begin();
	  for(; nl != nLoops.end(); ++nl){
	     std::cerr << "Head: " << ((*nl).header)->getName().str() << " Body: { ";
	     std::set<llvm::BasicBlock*>::iterator j = ((*nl).loop).begin();
	     std::vector<llvm::BasicBlock*> temp;
      	     for(; j != ((*nl).loop).end(); ++j){
	         if(*j != (*nl).header)
	             temp.push_back(*j);
	     } 
	     std::sort(temp.begin(), temp.end(), cmp);  
	     std::vector<llvm::BasicBlock*>::iterator out = temp.begin();
	     for(; out != temp.end(); ++out)
	         std::cerr << (*out)->getName().str() << " ";
	     std::cerr << "}\n";
	  }
      }


      //moving loop-invariant instructions
      //iterate over the natural loops detected earlier
      bool stop = true;
	do{
	  stop = true;
      std::vector<naturalLoop>::iterator nl = nLoops.begin();
      for(; nl != nLoops.end(); ++nl){
          //*nl contains the header and natural loop
          //create a list of all definitions in the natural loop
          useList.clear();
	  std::set<llvm::BasicBlock*>::iterator it = ((*nl).loop).begin();
	  for(; it != ((*nl).loop).end(); ++it){
	      for(BasicBlock::iterator instrIter = (*it)->begin(), instrEnd = (*it)->end(); instrIter != instrEnd; ++instrIter){
	          useList.push_back(instrIter);
	      }
 	  }

	  //iterate over the instructions in the loop body to determine loop invariant instructions
	  std::vector<llvm::Instruction*>::iterator instr = useList.begin();
  	  for(; instr != useList.end(); ++instr){
	      //check for exceptions
	      int opCode = (*instr)->getOpcode();
	      if(opCode != 14 && opCode != 15 && opCode != 16 && opCode != 17 && opCode != 18 && opCode != 19 && opCode != 26 && opCode != 27 && opCode != 28 && opCode != 29 && opCode != 30 && opCode != 31 && opCode != 32 && opCode != 48 && opCode != 5 && opCode != 47 && !((*instr)->isTerminator()) ){
		  bool instrCandidate = true;
	          llvm::User::op_iterator operIter = (*instr)->op_begin();
                  for (; operIter != (*instr)->op_end(); ++operIter){
		      if(isa<Instruction>(operIter)){
		          if(std::find(useList.begin(), useList.end(), cast<Instruction>(operIter)) == useList.end())	//not on the use list
			      instrCandidate = instrCandidate & true;
			  else
			      instrCandidate = instrCandidate & false;
		      }else if(isa<Constant>(operIter)){
		          instrCandidate = instrCandidate & true;    	
                      }else{
			  instrCandidate = instrCandidate & true;
		      }			
	          }
		  if(instrCandidate){
		      //a loop-invariant instruction is detected
		      if(PRINT_MOVING)
		          std::cerr << "moving instruction " << "%" << findKey(map, *instr) << "\n"; 
		      MovedLVInstructionCount++;
		      //reset the flag to cause a second iteration
		      stop = false;
		      llvm::BasicBlock *header = (*nl).header;		//the header
		      //determine if a unique pre header exists

		      if(header->getSinglePredecessor()){	//unique header exists
			  std::cerr << "Unique header\n";
		          //unlink instruction from BB
		          (*instr)->removeFromParent();
			  llvm::BasicBlock* preh = header->getUniquePredecessor();
			  preh->getInstList().insert(preh->getTerminator(), *instr);
		      }else{
			  //possibly create a pre-header
			  //iterate over the predecessors and determine if a unique one exists
			  std::vector<llvm::BasicBlock*> pre;
			  pred_iterator p = pred_begin(header);
		          std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator headDom = DominatorMap.find(header);
			  int numPred = 0;
			  llvm::BasicBlock *preHeader;
			  std::set<llvm::BasicBlock*>::iterator poss;
	                  for(; p != pred_end(header); ++p){
	      		      if((headDom->second).find(*p) != (headDom->second).end()){
			          //possible unique pre-header
			          numPred++;
			          poss = (headDom->second).find(*p);	  
			          pre.push_back(*p);
				  preHeader = *poss;
			      }
 	  		  }
			  if(numPred == 1){
			      //unique pre-header exists
		              (*instr)->removeFromParent();
			      preHeader->getInstList().insert(preHeader->getTerminator(), *instr);
			  }else{
			      //adding preheader
			      std::cerr << "adding preheader for loop with header " << header->getName().str() << "\n";
			      ArrayRef<BasicBlock*> ref(pre);  
			      preHeader = SplitBlockPredecessors(header, ref, "theFirst", NULL);
			      //add the instruction before the terminator
			      (*instr)->removeFromParent();
			      preHeader->getInstList().insert(preHeader->getTerminator(), *instr);
			  }
		      }		      
		  }
 	      }  
          }
      }
   }while(!stop);

    if(MovedLVInstructionCount > 0)
        return true;
    else
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
  RegisterPass<loopInv> X("loopInv", "Loop-invariant code motion analysis",
			   false, true);
}
