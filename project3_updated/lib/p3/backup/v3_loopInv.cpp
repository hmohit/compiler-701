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
#include "naturalLoop.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

STATISTIC(MovedLVInstructionCount, "Number of loop-invariant instructions moved.");


bool cmpFunction(naturalLoop a, naturalLoop b){
    if(a.loop.size() != b.loop.size())
        return a.loop.size() > b.loop.size();
    else
	return a.header->getName().str() > b.header->getName().str(); 
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
      bool done = false;		//flag to check if another iteration is required
      bool changed = false;

      //data structures for dominators
      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> > DominatorMap;
      std::vector<std::set<llvm::BasicBlock*> > Dominators;
     
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
//	      std::cerr << "The start node is: " << root << "\n";

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
//	  std::cerr << "Analyzing " << it->getName().str() << "\n";
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
//         std::set<llvm::BasicBlock*>::set &dom = (itr->second);		//dom points to current dominator set

//	 std::cerr << "Test\n";
//	 for(std::set<llvm::BasicBlock*>::iterator j = dom.begin(); j!= dom.end(); ++j){
//	      std::cerr << *j << " ";
//	 } 
// 	 std::cerr << "\n";

	 std::set<llvm::BasicBlock*> temp = allNodes;		//initialize to all nodes for 1st iteration
	 std::set<llvm::BasicBlock*> temp2;
	 pred_iterator pred = pred_begin(curr);
	 for(; pred != pred_end(curr); ++pred){
	     std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator predDom = DominatorMap.find(*pred); 
	     //predDom->second is the dominator set for block predDom
	     setIntersection(temp, (predDom->second), temp2);
	     temp = temp2;
	     temp2.clear();
//      	     for(std::set<llvm::BasicBlock*>::iterator i = temp.begin(); i != temp.end(); ++i)
//                 std::cerr << *i << " ";
//             std::cerr << "\n";
	 }
	 temp.insert(curr);
	 domWorkingSet.pop();

	 if(temp != (currDom->second)){
	     (currDom->second).clear();
	     (currDom->second).insert(temp.begin(), temp.end());
	     succ_iterator basicSucc = succ_begin(curr);
//	     std::cerr << "Successors for block " << curr->getName().str() << ": ";
 	     for(; basicSucc != succ_end(curr); ++basicSucc){
                 domWorkingSet.push(*basicSucc);
//		 std:: cerr << (*basicSucc)->getName().str() << " ";
	     }
//	     std::cerr << "\n";

	     std::cerr << curr->getName().str() << " Dominators are: ";
	     for(std::set<llvm::BasicBlock*>::iterator test = (currDom->second).begin(); test != (currDom->second).end(); ++test)
	         std::cerr << (*test)->getName().str() << " ";
	     std::cerr << "\n";
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
//	      std::cerr << "Analyzing " << BB->getName().str() << "\t";
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
//		          std::cerr << "Backedge found to new " << (*basicSucc)->getName().str() << " for " << BB->getName().str() << "\n";    
			  std::set<llvm::BasicBlock*> temp;
			  temp.insert(BB);
		          headerMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(*basicSucc, temp));
		      }else{
			  //the header has pre-existing backedges
//			  std::cerr << "Backedge found to existing " << (*basicSucc)->getName().str() << " for " << BB->getName().str() << "\n";
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
//      std::cerr << "\nLoop analysis:\n"; 
      std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >::iterator it = headerMap.begin();
      //iterate over all headers identified in previous step
      for(; it != headerMap.end(); ++it){
	  //header is the head node
          llvm::BasicBlock *header = it->first;
          std::set<llvm::BasicBlock*> tempLoop;
// 	  std::cerr << "Analyzing header " << header->getName().str() << "\n"; 
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
//		  std::cerr << "Analyzing back edge from " << nuc->getName().str() << "\n";
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
//	      std::cerr << "The loop body with header " << header->getName().str() << " contains: ";    
//	      std::set<llvm::BasicBlock*>::iterator test = tempLoop.begin();
//	      for(; test != tempLoop.end(); ++test)
//	          std::cerr << " " << (*test)->getName().str();
//	      std::cerr << "\n"; 
          }
	  //store the header and its loop
	  naturalLoop insertLoop(header, tempLoop);
	  nLoops.push_back(insertLoop);
//	  loops.headerList.push_back(header);
//	  loops.naturalMap.insert(std::pair<llvm::BasicBlock*, std::set<llvm::BasicBlock*> >(header, tempLoop));
      }

/*
      //Natural loops test
      std::vector<naturalLoop>::iterator i = nLoops.begin();
      for(; i != nLoops.end(); ++i){
          std::cerr << "The natural loop associated with header " << ((*i).header)->getName().str() << " are: ";
	  std::set<llvm::BasicBlock*>::iterator j = ((*i).loop).begin();
	  for(; j != ((*i).loop).end(); ++j)
	      std::cerr << " " << (*j)->getName().str();
	  std::cerr << "\n";
      }
*/

      //sort the natural loops
      std::sort(nLoops.begin(), nLoops.end(), cmpFunction);

/*
      std::cerr << "Sorted loops: \n";
      //Sorted natural loops test
      std::vector<naturalLoop>::iterator t1 = nLoops.begin();
      for(; t1 != nLoops.end(); ++t1){
          std::cerr << "The natural loop associated with header " << ((*t1).header)->getName().str() << " are: ";
	  std::set<llvm::BasicBlock*>::iterator j = ((*t1).loop).begin();
	  for(; j != ((*t1).loop).end(); ++j)
	      std::cerr << " " << (*j)->getName().str();
	  std::cerr << "\n";
      }
*/

      //moving loop-invariant instructions
      //iterate over the natural loops detected earlier
      bool stop = true;
//      while(!stop){ 
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

	  //useList test
//	  std::vector<llvm::Instruction*>::iterator test = useList.begin();
//	  std::cerr << "useList for " << ((*nl).header)->getName().str() << " contains: ";
//	  for(; test != useList.end(); ++test){
//	      std::cerr << "%" << findKey(map, *test) << " ";
//	  }
//	  std::cerr << "\n";

	  //iterate over the instructions in the loop body to determine loop invariant instructions
	  std::vector<llvm::Instruction*>::iterator instr = useList.begin();
  	  for(; instr != useList.end(); ++instr){
	      //check for exceptions
	      int opCode = (*instr)->getOpcode();
//	      std::cerr << (*instr)->getOpcode() << "\n";
	      if(opCode != 14 && opCode != 15 && opCode != 16 && opCode != 17 && opCode != 18 && opCode != 19 && opCode != 26 && opCode != 27 && opCode != 28 && opCode != 29 && opCode != 30 && opCode != 31 && opCode != 32 && opCode != 48 && opCode != 5 && opCode != 47 && !((*instr)->isTerminator())){
//	          std::cerr << "Candidate\n";
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
		      std::cerr << "We have a winner: " << "%" << findKey(map, *instr) << "for loop" << ((*nl).header)->getName().str() << "\n"; 
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
			  //create a pre-header
			  std::vector<llvm::BasicBlock*> pre;
			  pred_iterator p = pred_begin(header);
	                  for(; p != pred_end(header); ++p){
			      pre.push_back(*p);
 	  		  }
			  ArrayRef<BasicBlock*> ref(pre);  
			  llvm::BasicBlock *preHeader = SplitBlockPredecessors(header, ref, "theFirst", NULL);
			  //add the instruction before the terminator
			  (*instr)->removeFromParent();
			  preHeader->getInstList().insert(preHeader->getTerminator(), *instr);
//		          if((*nl).loop.find(pred_)))
		      }		      
		  }
 	      }  
          }
//	  std::cerr << "\n";

/*	  //uses list test
	  std::cerr << "Use list for loop " << ((*nl).header)->getName().str() << "are ";
	  std::vector<llvm::Instruction*>::iterator i = useList.begin();
	  for(; i != useList.end(); ++i)
              std::cerr << "%" << findKey(map, *i) << "\t";         
	  std::cerr << "\n"; */

      }
   }while(!stop);
   
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
