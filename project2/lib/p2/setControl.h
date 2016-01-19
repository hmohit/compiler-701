// The header file which contains the declarations of the functions needed to manipulate the instruction map
#ifndef SETCONTROL_H
#define SETCONTROL_H

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
    int addToSet(llvm::SmallSet<llvm::Instruction*, 10>&, llvm::Instruction*); 

    void printSet(std::set<llvm::Instruction*>&, llvm::DenseMap<llvm::Instruction*, int>& map);

    int findInSet(llvm::SmallSet<llvm::Instruction*, 10>&, llvm::Instruction*);

    void setDifference(std::set<llvm::Instruction*>&, std::set<llvm::Instruction*>&, std::set<llvm::Instruction*>&);

    void setUnion(std::set<llvm::Instruction*>&, std::set<llvm::Instruction*>&, std::set<llvm::Instruction*>&);

    

#endif
