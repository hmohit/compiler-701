// Functions to create a map with llvm::Instruction* as key & the instruction count as value

#include "instrMap.h"

using namespace llvm;
    
    // function which adds a new Instruction*, count pair to the map passed in
    int addToMap(llvm::DenseMap<llvm::Instruction*, int>& map, llvm::Instruction* instr){
        instrCount++;
        map[instr] = instrCount;
        return 0;
    }

    // a function which prints the current instruction count
    int printCount(){
        return instrCount;
    } 

    // a function which iterates over the map passed in, printing the key & value fields of the map
    int printMap(llvm::DenseMap<llvm::Instruction*, int>&map){
        llvm::DenseMap<llvm::Instruction*, int>::iterator i = map.begin();
        for(; i!= map.end(); ++i)
            std::cerr << "Key: " << i->first << "\tValue: " << i->second << "\n";
        return 0;
    }

    // a function which searches for the key in the map passed in. Returns 0 if unsuccessful or the instruction number on success
    int findKey(llvm::DenseMap<llvm::Instruction*, int>& map, llvm::Instruction* key){
        llvm::DenseMap<llvm::Instruction*, int>::iterator iter = map.find(key);
        if(iter == map.end())
            return 0;    
        else
            return iter->second;
    }

