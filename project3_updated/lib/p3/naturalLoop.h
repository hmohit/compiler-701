//The natural loop class
#ifndef NATURALLOOP_H
#define NATURALLOOP_H

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

class naturalLoop{
    public:
        llvm::BasicBlock *header;					//the header of the natural loop
        std::set<llvm::BasicBlock*> loop;				//map header to loop body
	naturalLoop(llvm::BasicBlock*, std::set<llvm::BasicBlock*>);	
        static bool cmpFunction(naturalLoop a, naturalLoop b);

};

#endif
