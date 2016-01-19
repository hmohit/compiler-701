#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <list>
#include "naturalLoop.h"

//sort function
bool naturalLoop::cmpFunction(naturalLoop a, naturalLoop b){
    if(a.loop.size() != b.loop.size())
        return a.loop.size() < b.loop.size();
    else
	return a.header->getName().str() < b.header->getName().str(); 
}

//constructor
naturalLoop::naturalLoop(llvm::BasicBlock *BB, std::set<llvm::BasicBlock*> L){
    header = BB;
    loop = L;
}
