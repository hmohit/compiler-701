// Functions to create a map with llvm::Instruction* as key & the instruction count as value

#include "setControl.h"
#include "instrMap.h"

using namespace llvm;
    
    // function which adds a new Instruction*, count pair to the map passed in
    int addToSet(std::set<llvm::Instruction*>& set, llvm::Instruction* instr){
        set.insert(instr);
        return 0;
    }

    // a function which iterates over the map passed in, printing the key & value fields of the map
    void printSet(std::set<llvm::Instruction*>& set, llvm::DenseMap<llvm::Instruction*, int>& map){
	std::list<int> temp;
	for(std::set<llvm::Instruction*>::iterator iter = set.begin(); iter != set.end(); ++iter){
//	    std::cerr << " %" << findKey(map, cast<llvm::Instruction>(*iter));
	    temp.push_back(findKey(map, cast<llvm::Instruction>(*iter))) ;
//	    std::cerr << *iter << "\t";
        }
	temp.sort();
	std::list<int>::iterator i = temp.begin();
	for(; i!= temp.end(); ++i)
	    std::cerr << " %" << *i;
    }

    // a function which searches for the key in the map passed in. Returns 0 if unsuccessful or the instruction number on success
    int findInSet(llvm::SmallSet<llvm::Instruction*, 10>& set, llvm::Instruction* instr){
	return set.count(instr);
    }

    void setDifference(std::set<llvm::Instruction*>& source1, std::set<llvm::Instruction*>& source2, std::set<llvm::Instruction*>& dest){
        std::set_difference(source1.begin(), source1.end(), source2.begin(), source2.end(), std::inserter(dest, dest.end())); 
    }

    void setUnion(std::set<llvm::Instruction*>& source1 , std::set<llvm::Instruction*>& source2, std::set<llvm::Instruction*>& dest){
        std::set_union(source1.begin(), source1.end(), source2.begin(), source2.end(), std::inserter(dest, dest.end())); 
    }

    void setIntersection(std::set<llvm::BasicBlock*>& source1 , std::set<llvm::BasicBlock*>& source2, std::set<llvm::BasicBlock*>& dest){
        std::set_intersection(source1.begin(), source1.end(), source2.begin(), source2.end(), std::inserter(dest, dest.end())); 
    }
