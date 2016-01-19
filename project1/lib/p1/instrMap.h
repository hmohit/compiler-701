// The header file which contains the declarations of the functions needed to manipulate the instruction map
#ifndef INSTRMAP_H
#define INSTRMAP_H

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

    // A static integer which keeps track of the number of instructions encountered
    static int instrCount;

    int addToMap(llvm::DenseMap<llvm::Instruction*, int>&, llvm::Instruction*); 

    int printCount();   

    int printMap(llvm::DenseMap<llvm::Instruction*, int>&);

    int findKey(llvm::DenseMap<llvm::Instruction*, int>&, llvm::Instruction*);

#endif
