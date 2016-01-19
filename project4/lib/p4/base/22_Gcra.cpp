//===-- Gcra.cpp - Graph-coloring Register Allocator --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===--------------------------------------------------------------------===//
//
// This file does Graph-coloring Register Allocation, for CS 701 Project 4.
//
//===--------------------------------------------------------------------===//

#define DEBUG_TYPE "gcra"
#include "flags.h"
#include <map>
#include "RDfact.h"
#include <stack>
#include <queue>
#include <iostream>

#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/MachineFunctionPass.h"

using namespace llvm;

typedef map<const MachineBasicBlock *, set<unsigned>*> BBtoRegMap;
typedef map<const MachineInstr *, set<unsigned>*> InstrToRegMap;
typedef map<const MachineBasicBlock *, set<RDfact *>*> BBtoRDfactMap;
typedef map<const MachineInstr *, set<RDfact *>*> InstrToRDfactMap;

namespace {
  class Gcra : public MachineFunctionPass {
  private:
    static const bool DEBUG = true;
    static const bool DEBUG_AVAIL = true;


#ifdef PRINTLIVE
    static const bool PRINT_LIVE = true;
#else
    static const bool PRINT_LIVE = false;
#endif

#ifdef PRINTRD
    static const bool PRINT_RD = true;
#else
    static const bool PRINT_RD = false;
#endif

#ifdef PRINTRANGES
    static const bool PRINT_RANGES = true;
#else
    static const bool PRINT_RANGES = false;
#endif
 
#ifdef PRINTGRAPH
    static const bool PRINT_GRAPH = true;
#else
    static const bool PRINT_GRAPH = false;
#endif
   
    // reg class -> non-spill regs for that class
    map<int, std::set<unsigned>*> regClassToAvailPregSetMap;

    set<RDfact *> RDfactSet;
    
    std::map<MachineInstr *, unsigned> InstrToNumMap;
    
    BBtoRegMap liveBeforeMap;
    BBtoRegMap liveAfterMap;
    BBtoRegMap liveVarsGenMap;
    BBtoRegMap liveVarsKillMap;
    InstrToRegMap insLiveBeforeMap;
    InstrToRegMap insLiveAfterMap;
    std::set<unsigned> *argPregSet;  // set of regs used to pass in args
    MachineBasicBlock *firstBB;      // first basic block in curr function

    BBtoRDfactMap RDbeforeMap;
    BBtoRDfactMap RDafterMap;
    BBtoRDfactMap RDgenMap;
    BBtoRDfactMap RDkillMap;
    InstrToRDfactMap insRDbeforeMap;
    InstrToRDfactMap insRDafterMap;

    MachineRegisterInfo *MRI;
    
    int numRegClasses;

    std::multimap<unsigned, std::set<MachineInstr *>*> initLiveRange;	//initial live range (reg -> instr)
    std::multimap<unsigned, std::set<MachineInstr *>*> finalLiveRange;	//initial live range (reg -> instr)
    std::multimap<unsigned, std::vector<unsigned>*> interferenceGraph;	//interference graph

    std::map<unsigned, std::set<unsigned>*> regToAvailMap;
    std::map<unsigned, unsigned> regToColorMap;				//map registers to their assigned colors
    std::map<MachineInstr*, int> instrToStackMap;
    std::map<MachineInstr*, unsigned> instrToPregMap;
    map<int, std::set<unsigned>*> regClassToSpillPregSetMap;		//spill registers for a class
    std::set<unsigned>spillRegistersAll;				//set of spill registers, including aliases
    std::set<unsigned>spillRegisters;					//set of spill registers without aliases
    std::set<int>usedRegClasses;
    std::map<unsigned, int> regToStackMap;    

  public:
    static char ID; // Pass identification, replacement for typeid
    
    //**********************************************************************
    // constructor
    //**********************************************************************
    Gcra() : MachineFunctionPass(ID) {
    }
    
    //**********************************************************************
    // runOnMachineFunction
    //
    //**********************************************************************
    bool runOnMachineFunction(MachineFunction &Fn) {
      if (DEBUG || PRINT_LIVE || PRINT_RD) {
	std::cerr << "START FUNCTION " << Fn.getFunction()->getName().str() << "\n";
      }

      // GET NUM REGISTER CLASSES
      getNumRegClasses(Fn);

      // INITIALIZE FOR EACH FN
      RDfactSet.clear();
      RDbeforeMap.clear();
      RDafterMap.clear();
      InstrToNumMap.clear();
      liveBeforeMap.clear();
      liveAfterMap.clear();
      liveVarsGenMap.clear();
      liveVarsKillMap.clear();
      insLiveBeforeMap.clear();
      insLiveAfterMap.clear();
      
      RDbeforeMap.clear();
      RDafterMap.clear();
      RDgenMap.clear();
      RDkillMap.clear();
      insRDbeforeMap.clear();
      insRDafterMap.clear();
     
      initLiveRange.clear(); 
      finalLiveRange.clear();
      interferenceGraph.clear();
      regToAvailMap.clear();
      regToColorMap.clear();
      regClassToSpillPregSetMap.clear();
      spillRegisters.clear();
      spillRegistersAll.clear();
      usedRegClasses.clear();      
      regToStackMap.clear();

      // STEP 1: get sets of regs, set of defs, set of RDfacts,
      //         instruction-to-number map
      if (! doInit(Fn)) {
	// no virtual registers in this function -- not much to do
	MRI->clearVirtRegs();
	return 0;
      }

      if (DEBUG) {
	printInstructions(Fn);
      }

      // STEP 2: live analysis for all registers (fill in globals
      //         liveBeforeMap and liveAfterMap for blocks, and
      //         globals insLiveBeforeMap and insLiveAfterMapfor
      //         instructions)
      if (DEBUG) {
	std::cerr << "START LIVE ANALYSIS\n";
      }
      doLiveAnalysis(Fn);
      if (PRINT_LIVE) {
	printLiveResults(Fn);
      }
      
      // STEP 2(a): add an RDfact to (global) RDfactSet for each
      //            preg used to pass an arg to this fn;
      //            must do this after live anal, since that's
      //            where we compute argPregSet
      addArgPregsToRDfactSet();
      
      // STEP 3: reaching defs analysis (fill in globals RDbeforeMap and
      //         RDafterMap for blocks, and globals insRDbeforeMap and
      //         insRDafterMap for instructions)
      if (DEBUG) {
	std::cerr << "\nSTART REACHING DEFS ANALYSIS\n";
      }
      doReachingDefsAnalysis(Fn);
      if (PRINT_RD) {
	printRDResults(Fn);
      }
      
      createLiveRanges(Fn);
      if(PRINT_RANGES)
          printLiveRange(Fn);

      combineRanges(Fn);
      if(PRINT_RANGES)
          printFinalRange(Fn);

      createInterferenceGraph(Fn);
      if(PRINT_GRAPH)
          printInterferenceGraph(Fn);
      std::cerr << "COMPLETED INTERFERENCE\n";

      colorInterferenceGraph(Fn);
      std::cerr << "COMPLETED COLORING\n";

      replaceVWithP(Fn);
      std::cerr << "COMPLETED REPLACING\n";
//      exit(0); // prevent coredump until reg alloc is implemented
      MRI->clearVirtRegs();
      return true;
    }
    
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      // Eliminate PHI nodes before we get the CFG.
      // This works by inserting copies into predecessor blocks.
      // So the code is no longer in SSA form.
      AU.addRequiredID(PHIEliminationID); 
      // This pass used to be required.  Including it now causes
      // a runtime error.
      //      AU.addRequiredID(TwoAddressInstructionPassID);
      MachineFunctionPass::getAnalysisUsage(AU);
    }
    
  private:
    //**********************************************************************
    // doInit
    //
    // fill in
    //  RDfactSet:     set of all reaching-def facts in this function
    //                 i.e., the universe of facts for reaching-defs
    //                       analysis
    //  InstrToNumMap: map from instruction to unique # (for debugging)
    //  vregToAvailPregSetMap
    //                 map from each vreg used in this fn to its available
    //                 set of pregs (taking into account the "allocation
    //                 order" and the "reserved regs" and not putting any
    //                 preg that occurs in this fn -- or any of its aliases --
    //                 in an available set)
    //
    // Return T iff there are vregs in this fn
    //**********************************************************************
    bool doInit(MachineFunction &Fn) {
      bool yesVregs = false;
      std::set<unsigned> usedPregSet;   // pregs that occur in this fn
                                        // useful when finding spill registers
      std::set<unsigned> vregSet;       // vregs defined in this fn
      MRI = &Fn.getRegInfo();
      const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
      
      // iterate over all basic blocks, all instructions in a block,
      // all operands in an instruction
      int insNum = 1;
      for (MachineFunction::iterator MFIt = Fn.begin(), MFendIt = Fn.end();
	   MFIt != MFendIt; MFIt++) {
	for (MachineBasicBlock::iterator MBBIt = MFIt->begin(),
	       MBBendIt = MFIt->end(); MBBIt != MBBendIt; MBBIt++) {
	  //*MBBIt is a MachineInstr
	  InstrToNumMap[MBBIt] = insNum;
	  insNum++;
	  int numOp = MBBIt->getNumOperands();
	  for (int i = 0; i < numOp; i++) {
	    MachineOperand &MOp = MBBIt->getOperand(i);  
	    if (MOp.isReg() && MOp.getReg()) {
	      unsigned reg = MOp.getReg();
	      // Here if this operand is
	      //  (a) a register
	      //  (b) not special reg 0
	      // Add it to vregSet or usedPregSet depending on whether
	      // it is a vreg or a preg; if a preg, also add all aliases
	      if (TargetRegisterInfo::isVirtualRegister(reg)) {
		vregSet.insert(reg);
		yesVregs = true;  // found a vreg!
		int vregClass = MRI->getRegClass(reg)->getID();
		usedRegClasses.insert(vregClass);
		//HERE
	      } else {
		usedPregSet.insert(reg);
		addAliases(&usedPregSet, reg, TRI);
	      }
	      if (MOp.isDef()) {
		RDfactSet.insert(new RDfact(reg, MBBIt));
	      } // end a def of a reg
	    } // end operand is a register
	  } // end for each operand
	} // end iterate over all instructions in 1 basic block
      } // end iterate over all basic blocks in this fn
      
      // now fill in regClassToAvailPregSetMap:
      // iterate over register classes (for this machine architecture)
      // for each, get its available set of pregs, taking into account
      // the "allocation order" and the "reserved regs" and the
      // set of pregs already used in this fn
      BitVector reservedRegs = TRI->getReservedRegs(Fn);
      for (int k=0; k<numRegClasses; k++) {
	set<unsigned> *availPregSet = new set<unsigned>();
	regClassToAvailPregSetMap[k] = availPregSet;
	const TargetRegisterClass *trc = TRI->getRegClass(k);
	ArrayRef<uint16_t> rawOrder = trc->getRawAllocationOrder(Fn);
	ArrayRef<uint16_t>::iterator rItr = rawOrder.begin();
	while (rItr != rawOrder.end()) {
	  if (reservedRegs.test(*rItr)) {
	    // this register is reserved -- do NOT add it to avail set
	    ++rItr;
	  } else {
	    //  add to avail set for this reg class
	    unsigned preg = *rItr;
	    availPregSet->insert(preg);
	    ++rItr;
	  }
	} // end iterate over rawOrder
	if (DEBUG_AVAIL) {
	  std::cerr << "Avail set for register class " << k << ": ";
	  printRegSet(availPregSet);
	} // end if DEBUG_AVAIL
      } // end iterate over register classes

      return yesVregs;
    } // end doInit


    //**********************************************************************
    // addAliases
    //
    // given: S         ptr to set of registers
    //        reg       (unsigned) one reg
    //        TRI       TargetRegisterInfo
    //
    // do: add all aliases of reg to S (only a preg has aliases)
    //**********************************************************************
    void addAliases(std::set<unsigned> *S, unsigned reg,
		    const TargetRegisterInfo *TRI) {
      if (TargetRegisterInfo::isPhysicalRegister(reg)) {
	MCRegAliasIterator *it = new MCRegAliasIterator(reg, TRI, false);
	while (it->isValid()) {
	  S->insert(**it);
	  ++(*it);
	}
      }      
    }
 
    //*********************************************************************
    //replaceVWithP
    //*********************************************************************

    void replaceVWithP(MachineFunction &Fn){
	std::cerr << "STARTED REPLACING\n";
 	assignStackForCalls(Fn);
	std::cerr << "assigned stack\n";
	subRegs(Fn);
	std::cerr << "subRegs completed\n";
	addSpills(Fn);	
   }


    int getStackSpace(unsigned reg, MachineFunction &Fn){
	//check if already assigned
	std::map<unsigned, int>::iterator st = regToStackMap.find(reg);
	if(st != regToStackMap.end()){
	    return st->second;
	}
	const TargetRegisterClass *RC = MRI->getRegClass(reg);
	int frameIndex = Fn.getFrameInfo()->CreateSpillStackObject(RC->getSize(), RC->getAlignment());
	regToStackMap.insert(std::pair<unsigned, int>(reg, frameIndex));
	return frameIndex;
    }

    void addSpills(MachineFunction &Fn){
	MachineRegisterInfo *MRI = &Fn.getRegInfo();
	const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
	const TargetInstrInfo *TII = Fn.getTarget().getInstrInfo();
	for (MachineFunction::iterator MF = Fn.begin(), MFendIt = Fn.end(); MF != MFendIt; MF++) {
	    for (MachineBasicBlock::iterator BB = MF->begin(), BBend = MF->end(); BB != BBend; BB++) {
		int numOp = BB->getNumOperands();
		unsigned pReg, reg;
		MachineInstr *instruction = BB;
		const MCInstrDesc &MCID = BB->getDesc();
		//replace vreg with color
      		unsigned spillReg;
		for (int i = 0; i < numOp; i++) {
		    MachineOperand &MOp = BB->getOperand(i);
		    if(MOp.isReg()){
			reg = MOp.getReg();	
		    	if (TargetRegisterInfo::isVirtualRegister(reg)){
			    //virtual reg: replace with color
			    pReg = regToColorMap[reg];
			    if (TargetRegisterInfo::isVirtualRegister(pReg)){
				//spilling
				const TargetRegisterClass *RC = MRI->getRegClass(pReg);
				int frameIndex = getStackSpace(pReg, Fn);//Fn.getFrameInfo()->CreateSpillStackObject(RC->getSize(), RC->getAlignment());
  				int vregClass = MRI->getRegClass(pReg)->getID();
				spillReg = pickSpillReg(BB, vregClass, TRI);
				//get a spill register spillReg for instruction BB
				//substitute spillReg for all occurences of pReg 
				bool doneLoad = false;
				bool doneStore = false;
			        MachineBasicBlock *MBB = BB->getParent();
				for(int op = 0; op < numOp; ++op){
		    		    MachineOperand &M = BB->getOperand(op);
			    	    if(M.isReg()){
					unsigned V = M.getReg();	
		    			if (TargetRegisterInfo::isVirtualRegister(V)){
			    		    unsigned Vr = regToColorMap[V];
					    if(Vr == pReg){					    
			            		M.substPhysReg(spillReg, *TRI);
			    			//check for instruction type
			    			if(M.isUse() && !doneLoad){
						    std::cerr << "loading ";
						    printReg(spillReg);
						    std::cerr << " from stack " << frameIndex << " for instruction " << InstrToNumMap[BB] << "\n";
						    TII->loadRegFromStackSlot(*MBB, BB, spillReg, frameIndex, RC, TRI);    
						    std::cerr << "Completed\n";
						    doneLoad = true;
						}
						if(M.isDef() && !doneStore){
						    MachineBasicBlock::iterator IT = BB;
						    IT++;
//						    MachineBasicBlock *MBB = IT->getParent();
						    std::cerr << "storing ";
						    printReg(spillReg);
						    std::cerr << " on stack " << frameIndex << " for instruction " << InstrToNumMap[BB] << "\n";
					    	    TII->storeRegToStackSlot(*MBB, IT, spillReg, true, frameIndex, RC, TRI);
						    std::cerr << "Completed store\n";
						    doneStore = true;
						}
					    }
					}
				    }
				}
			    }
			}
		    } 
	        }
	    }
	}
    }

    //return a spill register
    unsigned pickSpillReg(MachineInstr *I, int vregClass, const TargetRegisterInfo *TRI){
	std::set<unsigned> *avail = regClassToSpillPregSetMap[vregClass];
	int numOp = I->getNumOperands();
	//iterate over available spill registers
	std::set<unsigned>::iterator aR = avail->begin();
//	std::cerr << "For register class " << vregClass << " checked: \n";
	for(; aR != avail->end(); ++aR){
	    std::set<unsigned> *temp = new std::set<unsigned>();
	    unsigned RUC = *aR;		//register under consideration
	    temp->insert(RUC);
	    bool useable = true;
//	    printReg(RUC);
//	    std::cerr << ": ";
	    addAliases(temp, RUC, TRI);
//	    printRegSet(temp);
//	    std::cerr << ": "; 
	    for (int op = 0; op < numOp; op++) {
                MachineOperand &MOp = I->getOperand(op);
	        if(MOp.isReg()){
	            unsigned reg = MOp.getReg();
		    if (TargetRegisterInfo::isPhysicalRegister(reg)){
//			printReg(reg);
			if(temp->find(reg) != temp->end()){
			    useable = false;
			}
		    }
	        }
	    }
//	    std::cerr << "\n";
	    if(useable){
//		std::cerr << "and returned ";
//		printReg(RUC);
//		std::cerr << "\n";
		return RUC;
	    }
	}
    }

    void subRegs(MachineFunction &Fn){
	const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
	const TargetInstrInfo *TII = Fn.getTarget().getInstrInfo();
	for (MachineFunction::iterator MF = Fn.begin(), MFendIt = Fn.end(); MF != MFendIt; MF++) {
	    for (MachineBasicBlock::iterator BB = MF->begin(), BBend = MF->end(); BB != BBend; BB++) {
		int numOp = BB->getNumOperands();
		unsigned pReg, reg;
		MachineInstr *instruction = BB;
		const MCInstrDesc &MCID = BB->getDesc();
		//replace vreg with color
      		for (int i = 0; i < numOp; i++) {
		    MachineOperand &MOp = BB->getOperand(i);
		    if(MOp.isReg()){
			reg = MOp.getReg();	
		    	if (TargetRegisterInfo::isVirtualRegister(reg)){
			    //virtual reg: replace with color
			    pReg = regToColorMap[reg];
/*
			    std::cerr << "Replacing " ;
			    printReg(reg);
			    std::cerr << " with ";
			    printReg(pReg);
			    std::cerr << "\n";
*/
			    if (TargetRegisterInfo::isPhysicalRegister(pReg)){
				//no spilling
			        MOp.substPhysReg(pReg, *TRI);
			    }
			}
		    } 
	        }
		//handle calls
/*		const MCInstrDesc &MCID = BB->getDesc();
		if(MCID.isCall()){
		    printReg(reg);
		    std::cerr << " has a call\n";
		}
*/
		if(MCID.isCall()){
		    //push to stack
//		    int frameIndex = instrToStackMap[instruction];
//		    unsigned vreg = instrToPregMap[BB];
//		    unsigned preg = regToColorMap[vreg];
//		    std::cerr << frameIndex << " for " << InstrToNumMap[BB]<< "\n";
//		    std::cerr << "Pushing ";
//		    printReg(instrToPregMap[BB]);
//		    std::cerr << " for ";
//		    printReg(vreg);
//		    std::cerr << "onto the stack\n";
//		    const TargetRegisterClass *RC = MRI->getRegClass(vreg);
//		    MachineBasicBlock *MBB = BB->getParent();
//		    TII->storeRegToStackSlot(*MBB, BB, preg, true, frameIndex, RC, TRI);
		    //reload from stack
//		    MachineBasicBlock::iterator I = BB;
//		    I++;
//		    TII->loadRegFromStackSlot(*MBB, I, preg, frameIndex, RC, TRI);
		}
	    }
	}
    }
    
//    std::multimap<unsigned, std::set<MachineInstr *>*> finalLiveRange;

    void assignStackForCalls(MachineFunction &Fn){
	const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
	const TargetInstrInfo *TII = Fn.getTarget().getInstrInfo();
	//iterate over the live range to determine if it includes a call
	MachineRegisterInfo *MRI = &Fn.getRegInfo();
	std::multimap<unsigned, std::set<MachineInstr*>*>::iterator i = finalLiveRange.begin();		
	for(; i != finalLiveRange.end(); ++i){
	    unsigned reg = i->first;
	    //initial value of frame index: allocate if needed
	    int frameIndex = -1;
	    //only process for a virtual register
	    if (TargetRegisterInfo::isVirtualRegister(reg)){
//		std::cerr << "Entering\n";
	        const TargetRegisterClass *RC = MRI->getRegClass(reg);
		std::set<MachineInstr*> *instr = i->second;
		//iterate over the instructions in the live range
		std::set<MachineInstr*>::iterator j = instr->begin();
		for(; j != instr->end(); ++j){
		    MachineInstr *I = *j;
		    const MCInstrDesc &MCID = I->getDesc();
		    if(MCID.isCall()){
			if(frameIndex == -1){
			    frameIndex = Fn.getFrameInfo()->CreateSpillStackObject(RC->getSize(), RC->getAlignment());
//			    std::cerr << "Assigning " << frameIndex << " for ";
//			    printReg(reg);
//			    std::cerr << "\n";
			}
		        const TargetRegisterClass *RC = MRI->getRegClass(reg);
		        MachineBasicBlock *MBB = I->getParent();
			unsigned preg = regToColorMap[reg];
		        TII->storeRegToStackSlot(*MBB, I, preg, true, frameIndex, RC, TRI);
		        //reload from stack
		        MachineBasicBlock::iterator IT = I;
		        IT++;
		        TII->loadRegFromStackSlot(*MBB, IT, preg, frameIndex, RC, TRI);
/*
			instrToStackMap[I] = frameIndex;
			instrToPregMap[I] = reg;
			std::cerr << "Assigning " << frameIndex << " for ";
			printReg(instrToPregMap[I]);
			std::cerr << " and ";
			printReg(regToColorMap[instrToPregMap[I]]);
			std::cerr << " and %" << InstrToNumMap[I] << "\n";
			break;
*/
		    }
		}
	    }
	}
/*
	std::map<MachineInstr*, unsigned>::iterator j = instrToPregMap.begin();
	for(; j != instrToPregMap.end(); ++j){
	    printReg(j->second);
	    std::cerr << " and " ;
	    printReg(regToColorMap[j->second]);
	    std::cerr << "\n";
	}
*/
    }

    //*********************************************************************
    //colorInterferenceGraph
    //*********************************************************************

//    map<int, std::set<unsigned>*> regClassToSpillPregSetMap;		//spill registers for a class
//    std::set<unsigned>spillRegistersAll;				//set of spill registers, including aliases
//    std::set<unsigned>spillRegisters;					//set of spill registers without aliases

    void colorInterferenceGraph(MachineFunction &Fn){
	std::set<unsigned> *vRegList = new std::set<unsigned>();	//list of virtual registers
	std::set<unsigned> *pRegList = new std::set<unsigned>();	//list of physicl registers	
	std::deque<unsigned> *regStack = new std::deque<unsigned>();
	//populate lists
	MRI = &Fn.getRegInfo();
	//get spill registers for used register classes
	fillUsedRegClassMap(Fn);
	getSpillRegisters(Fn);
	populateRegLists(vRegList, pRegList);
	//push virtual registers
	pushVirtualRegisters(Fn, vRegList, regStack);
	//push physical registers
	pushPhysicalRegisters(Fn, pRegList, regStack);
	//pop nodes and initiate coloring
	popNodes(regStack, Fn);
    } 

//    std::multimap<unsigned, std::set<MachineInstr *>*> finalLiveRange;	//initial live range (reg -> instr)

    void fillUsedRegClassMap(MachineFunction &Fn){
	std::cerr << "Used reg classes are: ";
	std::set<int>::iterator i = usedRegClasses.begin();
	for(; i != usedRegClasses.end(); ++i){
	    std::cerr << *i << " ";
	}
	std::cerr << "\n";
    }

    void getSpillRegisters(MachineFunction &Fn){
//	std::map<int, std::set<unsigned>*>::iterator i = regClassToAvailPregSetMap.begin();	
	std::set<int>::iterator i = usedRegClasses.begin();
	for(; i != usedRegClasses.end(); ++i){
	    int vregClass = *i;
	    int numSpills = 0;
	    std::set<unsigned> *spills = new std::set<unsigned>();
	    //iterate through the available registers for this class
	    std::set<unsigned> *avail = regClassToAvailPregSetMap[vregClass];
	    //check the alias registers first
	    std::set<unsigned>::iterator alias = spillRegistersAll.begin();
	    for(; alias != spillRegistersAll.end(); ++alias){
		if(avail->find(*alias) != avail->end()){
		    //check if *alias can be used
		    if(checkForSpill(*alias, spills)){
			//can be used
			spills->insert(*alias);
			numSpills++;
		    }
		}
		if(numSpills == 3){
		    filledSpills(vregClass, spills, Fn);
		    break;
		}
	    }

	    if(numSpills == 3){
//		filledSpills(vregClass, spills, Fn);
		continue;
	    }

	    std::set<unsigned>::iterator aR = avail->begin();
	    for(; aR != avail->end(); ++aR){
		unsigned RUC = *aR;
	        if(checkForSpill(RUC, spills)){
		    //can be used
		    spills->insert(RUC);
		    numSpills++;
		}
		if(numSpills == 3){
		    //3 spill registers found - done
		    filledSpills(vregClass, spills, Fn);
	    	    break;
		}
	    }
	}
	std::map<int, std::set<unsigned>*>::iterator check = regClassToSpillPregSetMap.begin();
	for(; check != regClassToSpillPregSetMap.end(); ++check){
	    int clas = check->first;
	    std::set<unsigned> *spillCheck = new std::set<unsigned>();
	    spillCheck = regClassToSpillPregSetMap[clas];
	    std::cerr << "Spill for class " << clas << ": ";
	    printRegSet(spillCheck);
	}
	std::cerr << "All spills: ";
	printRegSet(spillRegisters);
	std::cerr << "\n";
	std::cerr << "All spills & aliases: ";
	printRegSet(spillRegistersAll);
	std::cerr << "\n";
    }

    bool checkForSpill(unsigned reg, std::set<unsigned> *spills){
	//check if reg is already used
	if(spillRegisters.find(reg) == spillRegisters.end()){
	    //hasn't been used as a spill yet
	    //check if it's in use
	    std::multimap<unsigned, std::set<MachineInstr *>*>::iterator used = finalLiveRange.find(reg);
	    std::set<unsigned>::iterator used2 = spills->find(reg);
	    if(used == finalLiveRange.end() && used2 == spills->end()){
	        //not in use, use as spill
	        return true; 
	    }else{
		//in use
		return false;
	    }
	}else{
	    //already used as a spill
	    return false;
	}
    }

    void filledSpills(int vregClass, std::set<unsigned> *spills, MachineFunction &Fn){
	const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
        //add to set of spill registers
	spillRegisters.insert(spills->begin(), spills->end()); 
	//add it's aliases to the other set
	std::set<unsigned> *aliasOfSpills = new std::set<unsigned>();
	std::set<unsigned>::iterator i = spills->begin();
	for(; i != spills->end(); ++i){
	    addAliases(aliasOfSpills, *i, TRI);    
	}        
	spillRegistersAll.insert(aliasOfSpills->begin(), aliasOfSpills->end());
	spillRegistersAll.insert(spills->begin(), spills->end());

	//add to the map
 
//        std::cerr << "Spill for class " << vregClass << ": ";
//	printRegSet(spills);
	regClassToSpillPregSetMap.insert(std::pair<int, std::set<unsigned>*>(vregClass, spills));
//	std::cerr << "that's : ";
//	std::set<unsigned>* test = regClassToSpillPregSetMap[vregClass];
//	printRegSet(test);
	return;
    }

    void populateRegLists(std::set<unsigned> *vList, std::set<unsigned> *pList){
	std::multimap<unsigned, std::vector<unsigned>*>::iterator regs = interferenceGraph.begin();
	for(; regs != interferenceGraph.end(); ++regs){
	    unsigned reg = regs->first;
	    if (TargetRegisterInfo::isPhysicalRegister(reg)){
		pList->insert(reg);
	    }else{
		vList->insert(reg);
	    }	
	}
    }

    void pushVirtualRegisters(MachineFunction &Fn, std::set<unsigned> *vList, std::deque<unsigned> *regStack){
        std::map<int, int> *availPerClass = new std::map<int, int>();	//keep trck of available registers per class
	getNumAvailReg(availPerClass);
	std::set<unsigned>::iterator list = vList->begin();
	bool done = false;
	while(!done){
	    ///check if easy node can be pushed
	    for(list = vList->begin(); list != vList->end(); ++list){
	        unsigned reg = *list;
//	        std::cerr << "Checking: ";
//	        printReg(reg);
	        //check if current register can be pushed
	        if(checkIfEasy(reg, availPerClass, regStack)){
//		    std::cerr << "Pushing ";
//		    printReg(reg);
//	 	    std::cerr << "onto stack\n";
		    regStack->push_front(reg);
		    if(list == vList->end()){
		        vList->erase(reg);
			break;
		    }else
		 	vList->erase(reg);
	        }
	    }
	    //push node with max number of neighbors
	    unsigned regToPush = 0;
	    int maxUnstacked = 0;
	    for(list = vList->begin(); list != vList->end(); ++list){
		unsigned RUT = *list;
		int unstacked = unstackedNeighbors(RUT, regStack);
		if (unstacked > maxUnstacked){
		    regToPush = RUT;
		    maxUnstacked = unstacked;
		} 
	    }
	    if(maxUnstacked != 0){
//	        std::cerr << "Pushing max ";
//	        printReg(regToPush);
 //	        std::cerr << "onto stack\n";
	        regStack->push_front(regToPush);
	        vList->erase(regToPush);
	    }
	    if(vList->empty())
		done = true;
        }
    }

    bool checkIfEasy(unsigned reg, std::map<int, int> *avail, std::deque<unsigned> *regStack){
	int vregClass = MRI->getRegClass(reg)->getID();
	std::map<int, int>::iterator i = avail->find(vregClass);
	if(i != avail->end()){
	    int numAvail = i->second;
//	    std::cerr << "Number available for " << vregClass << " is " << numAvail << "\n";
	    //get the number of neighbours
	    int numNeighbors = unstackedNeighbors(reg, regStack);
	    if(numAvail > numNeighbors){
//	        (i->second)--;
		return true;
	    }else
	        return false;
	}
    }

    int unstackedNeighbors(unsigned reg, std::deque<unsigned> *regStack){
        int numNeighbors = 0;
	std::map<unsigned, std::vector<unsigned>*>::iterator j = interferenceGraph.find(reg);
	if(j != interferenceGraph.end()){
	    std::vector<unsigned> *temp = j->second;
	    std::set<unsigned> *neigh = new std::set<unsigned>(temp->begin(), temp->end());
	    std::set<unsigned>::iterator n = neigh->begin();
	    for(; n != neigh->end(); ++n){
	        if(std::find(regStack->begin(), regStack->end(), *n) == regStack->end()){
	            numNeighbors++;	
		}
	    } 
	}
//	printReg(reg);
//	std::cerr << " has " << numNeighbors << " unstacked neighbors\n";
	return numNeighbors;	 
    }

    std::set<unsigned>* popNeighbors(unsigned reg, std::deque<unsigned> *regStack, const TargetRegisterInfo *TRI){
        int numNeighbors = 0;
	std::set<unsigned> *neighAlias = new std::set<unsigned>();
	std::map<unsigned, std::vector<unsigned>*>::iterator j = interferenceGraph.find(reg);
	if(j != interferenceGraph.end()){
	    std::vector<unsigned> *temp = j->second;
	    std::set<unsigned> *neigh = new std::set<unsigned>(temp->begin(), temp->end());
	    std::set<unsigned>::iterator n = neigh->begin();
//	    printReg(reg);
//	    std::cerr << " checking: ";
	    for(; n != neigh->end(); ++n){
	        if(std::find(regStack->begin(), regStack->end(), *n) == regStack->end()){
		    if(TargetRegisterInfo::isPhysicalRegister(*n)){
//		        printReg(*n);
//		        std::cerr << " ";
//		        std::cerr << " which is popped\n";
	                neighAlias->insert(*n);
		        addAliases(neighAlias, *n, TRI);	
		    }else{
			neighAlias->insert(regToColorMap[*n]);
			addAliases(neighAlias, regToColorMap[*n], TRI);
		    }
/*
		    std::cerr << "Aliases for ";
		    printReg(*n);
		    if(TargetRegisterInfo::isVirtualRegister(*n)){
			std::cerr << " and ";
			printReg(regToColorMap[*n]);
		    }
		    std::cerr << " are ";
		    printRegSet(neighAlias);
*/
		}
	    } 
//	    std::cerr < "\n";
	}
/*
	printReg(reg);
	std::cerr << "cannot use: ";
	printRegSet(neighAlias);
*/
//	std::cerr << " has " << numNeighbors << " unstacked neighbors\n";
	return neighAlias;	 
    }

    void getNumAvailReg(std::map<int, int> *map){
	std::map<unsigned, std::set<unsigned>*>::iterator reg = regToAvailMap.begin();
	for(; reg != regToAvailMap.end(); ++reg){
//	    printReg(reg->first);
	    if (TargetRegisterInfo::isVirtualRegister(reg->first)){
	        int vregClass = MRI->getRegClass(reg->first)->getID();
	    	int numAvail = 0;//regClassToAvailPregSetMap[vregClass]->size() - regClassToSpillPregSetMap[vregClass]->size();
		std::set<unsigned> *pAvail = regClassToAvailPregSetMap[vregClass];
		std::set<unsigned>::iterator i = pAvail->begin();
		for(; i != pAvail->end(); ++i){
		    if(spillRegistersAll.find(*i) == spillRegistersAll.end())
			numAvail++;	    
		}
	    	map->insert(std::pair<int, int>(vregClass, numAvail));
//		int temo = map[vregClass];
		std::cerr << "Number of registers available for " << vregClass << " is " << numAvail << "\n";
	    }	    
	}
    }

    void pushPhysicalRegisters(MachineFunction &Fn, std::set<unsigned> *pList, std::deque<unsigned> *regStack){
	while(!pList->empty()){
	    regStack->push_front(*pList->begin());
	    pList->erase(pList->begin());
	}
    }

    void popNodes(std::deque<unsigned> *rStack, MachineFunction &Fn){
	while(!rStack->empty()){
	    unsigned reg = rStack->front();
//	    std::cerr << "Popping ";
//	    printReg(reg);
//	    std::cerr << " from stack\n";
	    if (TargetRegisterInfo::isPhysicalRegister(reg)){
  		//if physical register, no choice
		regToColorMap[reg] = reg;
	    }else{
		unsigned use = popVirtualReg(reg, rStack, Fn);	
		regToColorMap[reg] = use;
	    } 
	    rStack->pop_front();
	}
	
	std::map<unsigned, unsigned>::iterator i = regToColorMap.begin();
	for(; i != regToColorMap.end(); ++i){
	    std::cerr << "Color chosen for ";
	    printReg(i->first);	
	    std::cerr << " is ";
	    printReg(i->second);
	    if(TargetRegisterInfo::isVirtualRegister(i->first)){
		std::cerr << " for register class " << MRI->getRegClass(i->first)->getID();
	    }
	    std::cerr << "\n";
	}

    }

    unsigned popVirtualReg(unsigned reg, std::deque<unsigned> *rStack, MachineFunction &Fn){
	const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
	//get the list of available registers
//	std::map<int, int> *availPerClass = new std::map<int, int>();	//keep trck of available registers per class
//	getNumAvailReg(availPerClass);
        int vregClass = MRI->getRegClass(reg)->getID();
	std::set<unsigned> *avail = regClassToAvailPregSetMap[vregClass];
	std::set<unsigned>::iterator i = avail->begin();
        std::set<unsigned> *n = popNeighbors(reg, rStack, TRI);
	unsigned RUC;
	for(; i != avail->end(); ++i){
	    //build up the set of R and its aliases
	    RUC = *i;   
	    std::set<unsigned> *alloc = new std::set<unsigned>();
	    alloc->insert(RUC); 
	    addAliases(alloc, RUC, TRI);     
	    std::set<unsigned> *temp = new std::set<unsigned>();
	    std::set_intersection(alloc->begin(), alloc->end(), n->begin(), n->end(), std::inserter(*temp, temp->begin()));
	    //check if the register under consideration is already allocated
	    if(temp->empty() && (spillRegistersAll.find(RUC) == spillRegistersAll.end())){
		return RUC;
	    }
	    if(i == avail->end()){
		std::cerr << "No color a\n";
		return RUC;
	    }
	    //no registers available
	}
	std::cerr << "No color available for ";
	printReg(reg);
	std::cerr << "\n";
	return reg;
    }

    //*********************************************************************
    //createInterferenceGraph
    //
    //compute a node's neighbours 
    //*********************************************************************
//     map<int, std::set<unsigned>*> regClassToAvailPregSetMap;

    void createInterferenceGraph(MachineFunction &Fn){
	//create a map of the available registers and their aliases for all used registers
	createAvailRegSet(Fn);
	//iterate over all the registers in the final live range to determine interfering nodes
	std::multimap<unsigned, std::set<MachineInstr *>*>::iterator range = finalLiveRange.begin();
	for(; range != finalLiveRange.end(); ++range){
	    unsigned reg = range->first;	//the register under consideration
	    std::set<MachineInstr *> *list = range->second;	//it's corresponding live range

	    std::multimap<unsigned, std::set<MachineInstr *>*>::iterator check = finalLiveRange.begin(); 
	    std::vector<unsigned> *graph = new std::vector<unsigned>();

	    //check for disjoint CFG nodes
	    for(; check != finalLiveRange.end(); ++check){	//can't interfere with itself
		std::set<MachineInstr *> *cList = check->second;
		unsigned cReg= check->first;
		//iterate over the instructions in the final live range
		bool couldInterfere = false;
		std::set<MachineInstr*> *intInstr = new std::set<MachineInstr*>();
		std::set_intersection(list->begin(), list->end(), cList->begin(), cList->end(), std::inserter(*intInstr, intInstr->begin()));
/*
		for(std::set<MachineInstr *>::iterator i = list->begin(); i != list->end(); ++i){
		    if(cList->find(*i) != cList->end()){
			couldInterfere = true;
//			std::cerr << "possible interference\n";
			break;
		    }
		}		*/
    	
		if(!intInstr->empty() && reg != cReg){
		    //if the CFGs overlap, check for overlap in available registers
		    std::set<unsigned> *UUT = regToAvailMap[reg];	//avail reg for node under test
		    std::set<unsigned> *UTC = regToAvailMap[cReg];	//avail reg for comparison
		    std::set<unsigned> *temp = new std::set<unsigned>();
		    std::set_intersection(UUT->begin(), UUT->end(), UTC->begin(), UTC->end(), std::inserter(*temp, temp->begin()));
//		    std::cerr << "intersection of ";
//		    printReg(reg);
//		    std::cerr << " and ";
//		    printReg(cReg);
//		    std::cerr << "is :";
//		    printRegSet(temp);
		    if(!temp->empty()){
//			std::cerr << "Definetly interfering\n";
/*
			std::cerr << "Adding ";
			printReg(cReg);
			std::cerr << " to ";
			printReg(reg);
			std::cerr << "'s neighbor list\n";			
*/
			graph->push_back(cReg);
		    }
	        }
	    }		
//	std::cerr << "Interference graph for ";
//	printReg(reg);
//	std::cerr << "is : ";
//	printRegSet(graph);
	interferenceGraph.insert(std::pair<unsigned, std::vector<unsigned>*>(reg, graph));
	}
    }

    void createAvailRegSet(MachineFunction &Fn){
	std::multimap<unsigned, std::set<MachineInstr *>*>::iterator range = finalLiveRange.begin();
	for(; range != finalLiveRange.end(); ++range){
	    unsigned reg = range->first;	//the register under consideration
	    std::set<unsigned> *availReg = new std::set<unsigned>();
	    std::set<unsigned> *finalList = new std::set<unsigned>();
	    if(TargetRegisterInfo::isVirtualRegister(reg)){	//virtual register
	        //get the class of the virtual register
      	        MRI = &Fn.getRegInfo();
	        int vregClass = MRI->getRegClass(reg)->getID();
//		printReg(reg);
//		std::cerr << " belongs to register class " << vregClass << "\n";
	        availReg = regClassToAvailPregSetMap[vregClass];	//the set of available physical registers
	    }else{	//physical register
		availReg->insert(reg); 
	    }  
	    //add all aliases to the set
	    std::set<unsigned>::iterator i = availReg->begin();
	    for(; i != availReg->end(); ++i){
		const TargetRegisterInfo *TRI = Fn.getTarget().getRegisterInfo();
		addAliases(finalList, *i, TRI);		
		finalList->insert(*i);
	    }    
//	    std::set<unsigned>::iterator j = finalList->begin();
//	    for(; j != finalList->end(); ++j){
//		std::set<unsigned>::iterator i = availReg->begin()i
//	    
//	    }
/*
	    std::cerr << "Available registers for " ;
	    printReg(reg);
	    std::cerr << " :  ";	    
	    printRegSet(finalList);    
*/
	    regToAvailMap.insert(std::pair<unsigned, std::set<unsigned>*>(reg, finalList));
	}
    }

    //*********************************************************************
    //printInterferenceGraph
    //
    //print the interference graph
    //*********************************************************************

    void printInterferenceGraph(MachineFunction &Fn){
	std::cerr << "\nINTERFERENCE GRAPH FOR FUNCTION " << Fn.getFunction()->getName().str() << "\n";
	printInterferencePhysical();
	printInterferenceVirtual();
	std::cerr << "\n";
    }

    void printInterferencePhysical(){
	std::cerr << "\nPhysical Registers\n";
    	std::multimap<unsigned, std::vector<unsigned>*>::iterator i = interferenceGraph.begin(); 
	for(; i != interferenceGraph.end(); ++i){
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isPhysicalRegister(reg)) {
  	        printReg(reg);
       	        std::cerr << "'s neighbors: { " ;
		std::vector<unsigned> *temp = i->second;
//                std::set<unsigned> *graph = new std::set<unsigned>(temp->begin(), temp->end());
//	        graph = i->second;
		for(std::vector<unsigned>::iterator j = temp->begin(); j != temp->end(); ++j){
	            printReg(*j);
		    std::cerr << " ";
		}
		std::cerr << "}\n";
	    }
	}
    }

    void printInterferenceVirtual(){
	std::cerr << "\nVirtual Registers\n";
    	std::multimap<unsigned, std::vector<unsigned>*>::iterator i = interferenceGraph.begin(); 
	for(; i != interferenceGraph.end(); ++i){
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isVirtualRegister(reg)) {
  	        printReg(reg);
//	        std::cerr << "'s neighbors: " ;
  	        std::cerr << "'s neighbors: { " ;
		std::vector<unsigned> *temp = i->second;
//                std::set<unsigned> *graph = new std::set<unsigned>(temp->begin(), temp->end());
//	        graph = i->second;
		for(std::vector<unsigned>::iterator j = temp->begin(); j != temp->end(); ++j){
	            printReg(*j);
		    std::cerr << " ";
		}
		std::cerr << "}\n";

//                std::set<unsigned> *graph = new std::set<unsigned>();
//	        graph = i->second;
//	        printRegSet(graph);
	    }
	}
    }

    //**********************************************************************
    //combineRanges
    //
    //combine live ranges
    //**********************************************************************

    void combineRanges(MachineFunction &Fn){
	//iterate over the live ranges and combine overlapping ranges
	std::multimap<unsigned, std::set<MachineInstr *>*>::iterator itRange = initLiveRange.begin();
	while(itRange != initLiveRange.end()){
	    unsigned reg = itRange->first;
	    std::set<MachineInstr *> *list = itRange->second;	//list under consideration
            std::set<MachineInstr *> *combined = new std::set<MachineInstr *>();
	    combined->insert(list->begin(), list->end());
	    std::multimap<unsigned, std::set<MachineInstr *>*>::iterator i = itRange;
	    ++i;
	    for(; i != initLiveRange.end(); ++i){
		std::set<MachineInstr *> *nList = i->second;	//next list
		if(i->first == reg){
		    for(std::set<MachineInstr *>::iterator j=nList->begin(); j != nList->end(); ++j){
		        if(combined->find(*j) != combined->end()){
			    combined->insert(nList->begin(), nList->end());
			    itRange++;
			    break;
		        }
		    }
	        }
	    }
	    //push combined list onto map
	    finalLiveRange.insert(std::pair<unsigned, std::set<MachineInstr *>*>(reg, combined));
	    itRange++;
	}
    }

    //**********************************************************************
    //createLiveRanges
    //**********************************************************************

    void createLiveRanges(MachineFunction &Fn){
        for (MachineFunction::iterator bb = Fn.begin(), bbEnd = Fn.end(); bb != bbEnd; bb++) {
	    int firstInstr = 0;
	    for (MachineBasicBlock::iterator instr = bb->begin(); instr != bb->end(); instr++) {
		MachineBasicBlock *Basic = bb;
		//iterate over instructions and determine live range for registers defined
    		MachineInstr *currInstr = instr;
		set<unsigned> *instrDef = getOneInstrRegDefs(currInstr);
		if(Basic == firstBB && firstInstr == 0){
		    firstInstr = 1;
		    for (std::set<unsigned>::iterator IT = argPregSet->begin(); IT != argPregSet->end(); IT++) {
	  		instrDef->insert(*IT);
		    }
		    findRangeFirst(instrDef, currInstr, Fn);
		}else{
		    findRange(instrDef, currInstr, Fn);	
		}
	    }
	}      
    }

    //**********************************************************************
    //findRange
    //
    //given a set of registers, find the live range
    //
    //**********************************************************************

    void findRange(std::set<unsigned> *s, MachineInstr *instr, MachineFunction &Fn){
	for(std::set<unsigned>::iterator lIt = s->begin(); lIt != s->end(); lIt++){
            std::set<MachineInstr*> *regRange = new std::set<MachineInstr*>();	//store reg live range
	    unsigned reg = *lIt;
	    regRange->insert(instr);	    
	    addToRange(regRange, reg, Fn, instr);
	    unsigned *regPtr = &reg;
	    initLiveRange.insert(std::pair<unsigned, std::set<MachineInstr*>*>(reg, regRange));
	}	
    }

    void findRangeFirst(std::set<unsigned> *s, MachineInstr *instr, MachineFunction &Fn){
	for(std::set<unsigned>::iterator lIt = s->begin(); lIt != s->end(); lIt++){
            std::set<MachineInstr*> *regRange = new std::set<MachineInstr*>();	//store reg live range
	    unsigned reg = *lIt;
	    regRange->insert(instr);	    
	    addToRangeFirst(regRange, reg, Fn, instr);
	    unsigned *regPtr = &reg;
	    initLiveRange.insert(std::pair<unsigned, std::set<MachineInstr*>*>(reg, regRange));
	}	
    }

    void addToRange(std::set<MachineInstr*> *range, unsigned reg, MachineFunction &Fn, MachineInstr *I){
        for (MachineFunction::iterator bb = Fn.begin(), bbEnd = Fn.end(); bb != bbEnd; bb++) {
	    int firstInstr = 0;
	    for (MachineBasicBlock::iterator instr = bb->begin(); instr != bb->end(); instr++) {
		MachineBasicBlock *Basic = bb;
		//iterate over instructions to determine live range for registers in the set
    		MachineInstr *currInstr = instr;
		std::set<unsigned> *liveBefore = insLiveBeforeMap[currInstr];		
		//check if current reg is in live before set
		std::set<unsigned>::iterator isPresent = liveBefore->find(reg);
		if(isPresent != liveBefore->end()){
		    //register is present in live before set	
		    //check if this definition of the register reaches instruction currInstr
		    std::set<RDfact*> *reach = insRDbeforeMap[currInstr];
	    	    RDfact *currFact = new RDfact(reg, I);	     
		    std::set<RDfact*>::iterator doesItReach = reach->begin();
		    for(; doesItReach != reach->end(); ++doesItReach){
			RDfact *test = *doesItReach;
		        if(test->getReg() == reg && test->getInstr() == I){
		    	    range->insert(currInstr);
		        }
		    }
		}
	    }
	} 
    }

    void addToRangeFirst(std::set<MachineInstr*> *range, unsigned reg, MachineFunction &Fn, MachineInstr *I){
        for (MachineFunction::iterator bb = Fn.begin(), bbEnd = Fn.end(); bb != bbEnd; bb++) {
	    int firstInstr = 0;
	    for (MachineBasicBlock::iterator instr = bb->begin(); instr != bb->end(); instr++) {
		MachineBasicBlock *Basic = bb;
		//iterate over instructions to determine live range for registers in the set
    		MachineInstr *currInstr = instr;
		std::set<unsigned> *liveBefore = insLiveBeforeMap[currInstr];		
		//check if current reg is in live before set
		std::set<unsigned>::iterator isPresent = liveBefore->find(reg);
		if(isPresent != liveBefore->end()){
		    //register is present in live before set	
		    //check if this definition of the register reaches instruction currInstr
		    std::set<RDfact*> *reach = insRDbeforeMap[currInstr];
	    	    RDfact *currFact = new RDfact(reg, I);	     
		    std::set<RDfact*>::iterator doesItReach = reach->begin();
		    for(; doesItReach != reach->end(); ++doesItReach){
			RDfact *test = *doesItReach;
		        if(test->getReg() == reg && (test->getInstr() == I || test->getInstr() == 0)){
		    	    range->insert(currInstr);
		        }
		    }
		}
	    }
	} 
    }

    void printLiveRange(MachineFunction &Fn){
	std::cerr << "\nINITIAL LIVE RANGES FOR FUNCTION " << Fn.getFunction()->getName().str() << "\n";
	printLiveRangePhysical();
	printLiveRangeVirtual();
	std::cerr << "\n";
    }

    void printFinalRange(MachineFunction &Fn){
	std::cerr << "\nFINAL LIVE RANGES FOR FUNCTION " << Fn.getFunction()->getName().str() << "\n";
	printFinalLiveRangePhysical();
	printFinalLiveRangeVirtual();
	std::cerr << "\n";
    }

    void printLiveRangePhysical(){
	std::cerr << "\nPhysical Registers\n";
	std::multimap<unsigned, std::set<MachineInstr*>*>::iterator i = initLiveRange.begin();	
	for(; i != initLiveRange.end(); i++){
	    std::set<MachineInstr*> *S = i->second;
	    std::vector<unsigned> temp;
	    for(std::set<MachineInstr*>::iterator j=S->begin(); j!= S->end(); ++j){
		unsigned no = InstrToNumMap[*j];
		temp.push_back(no);
	    }
	    std::sort(temp.begin(), temp.end());
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isPhysicalRegister(reg)) {
  		printReg(reg);
	        std::cerr << ": { " ;
	        for(std::vector<unsigned>::iterator j=temp.begin(); j!= temp.end(); ++j){
	            std::cerr << "%" << *j << " ";
	        }   
	        std::cerr << "}\n";
	    }
	}
    }

    void printLiveRangeVirtual(){
	std::cerr << "\nVirtual Registers\n";
	std::multimap<unsigned, std::set<MachineInstr*>*>::iterator i = initLiveRange.begin();	
	for(; i != initLiveRange.end(); i++){
	    std::set<MachineInstr*> *S = i->second;
	    std::vector<unsigned> temp;
	    for(std::set<MachineInstr*>::iterator j=S->begin(); j!= S->end(); ++j){
		unsigned no = InstrToNumMap[*j];
		temp.push_back(no);
	    }
	    std::sort(temp.begin(), temp.end());
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isVirtualRegister(reg)) {
  		printReg(reg);
	        std::cerr << ": { " ;
	        for(std::vector<unsigned>::iterator j=temp.begin(); j!= temp.end(); ++j){
	            std::cerr << "%" << *j << " ";
	        }   
	        std::cerr << "}\n";
	    }
	}
    }

    void printFinalLiveRangePhysical(){
	std::cerr << "\nPhysical Registers\n";
	std::multimap<unsigned, std::set<MachineInstr*>*>::iterator i = finalLiveRange.begin();	
	for(; i != finalLiveRange.end(); i++){
	    std::set<MachineInstr*> *S = i->second;
	    std::vector<unsigned> temp;
	    for(std::set<MachineInstr*>::iterator j=S->begin(); j!= S->end(); ++j){
		unsigned no = InstrToNumMap[*j];
		temp.push_back(no);
	    }
	    std::sort(temp.begin(), temp.end());
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isPhysicalRegister(reg)) {
  		printReg(reg);
	        std::cerr << ": { " ;
	        for(std::vector<unsigned>::iterator j=temp.begin(); j!= temp.end(); ++j){
	            std::cerr << "%" << *j << " ";
	        }   
	        std::cerr << "}\n";
	    }
	}
    }

    void printFinalLiveRangeVirtual(){
	std::cerr << "\nVirtual Registers\n";
	std::multimap<unsigned, std::set<MachineInstr*>*>::iterator i = finalLiveRange.begin();	
	for(; i != finalLiveRange.end(); i++){
	    std::set<MachineInstr*> *S = i->second;
	    std::vector<unsigned> temp;
	    for(std::set<MachineInstr*>::iterator j=S->begin(); j!= S->end(); ++j){
		unsigned no = InstrToNumMap[*j];
		temp.push_back(no);
	    }
	    std::sort(temp.begin(), temp.end());
	    unsigned reg = i->first;
	    if (TargetRegisterInfo::isVirtualRegister(reg)) {
  		printReg(reg);
	        std::cerr << ": { " ;
	        for(std::vector<unsigned>::iterator j=temp.begin(); j!= temp.end(); ++j){
	            std::cerr << "%" << *j << " ";
	        }   
	        std::cerr << "}\n";
	    }
	}
    }

    //**********************************************************************
    // doLiveAnalysis
    //**********************************************************************
    void doLiveAnalysis(MachineFunction &Fn) {
      // initialize live maps to empty
      liveBeforeMap.clear();
      liveAfterMap.clear();
      liveVarsGenMap.clear();
      liveVarsKillMap.clear();
      insLiveBeforeMap.clear();
      insLiveAfterMap.clear();
      
      analyzeBasicBlocksLiveVars(Fn);
      analyzeInstructionsLiveVars(Fn);
    }
    
    //**********************************************************************
    // doReachingDefsAnalysis
    //**********************************************************************
    void doReachingDefsAnalysis(MachineFunction &Fn) {
      analyzeBasicBlocksRDefs(Fn);
      analyzeInstructionsRDefs(Fn);
    }
    
    //**********************************************************************
    // analyzeBasicBlocksLiveVars
    //
    // iterate over all basic blocks bb
    //    bb.gen = all upwards-exposed uses in bb
    //    bb.kill = all defs in bb
    //    put bb on the worklist
    //
    // also fill in (globals) firstBB, argPregSet
    //**********************************************************************d
    void analyzeBasicBlocksLiveVars(MachineFunction &Fn) {
      
      // initialize all before/after/gen/kill sets and
      // put all basic blocks on the worklist
      set<MachineBasicBlock *> worklist;
      firstBB = 0;
      MachineInstr *firstInstr = 0;      // first instruction in curr function
      for (MachineFunction::iterator MFIt = Fn.begin(), MFendIt = Fn.end(); MFIt != MFendIt; MFIt++) {
	if (firstInstr == 0) {
	  firstBB = MFIt;
	  MachineBasicBlock::iterator MBBIt = MFIt->begin();
	  //*MBBIt is a MachineInstr
	  firstInstr = MBBIt;
	}
	liveBeforeMap[MFIt] = new set<unsigned>();
	liveAfterMap[MFIt] = new set<unsigned>();
	liveVarsGenMap[MFIt] = getUpwardsExposedUses(MFIt);
	liveVarsKillMap[MFIt] = getAllDefs(MFIt);
	worklist.insert(MFIt);
      }
      
      // while the worklist is not empty {
      //   remove one basic block bb
      //   compute new bb.liveAfter = union of liveBefore's of all successors
      //   replace old liveAfter with new one
      //   compute new bb.liveBefore = (bb.liveAfter - bb.kill) union bb.gen
      //   if bb.liveBefore changed {
      //      replace old liveBefore with new one
      //      add all of bb's predecessors to the worklist
      //   }
      // }
      while (! worklist.empty()) {
	// remove one basic block and compute its new liveAfter set
	set<MachineBasicBlock *>::iterator oneBB = worklist.begin();
	MachineBasicBlock *bb = *oneBB;
	worklist.erase(bb);
	
	set<unsigned> *newLiveAfter = computeLiveAfter(bb);
	
	// update the liveAfter map
	liveAfterMap.erase(bb);
	liveAfterMap[bb] = newLiveAfter;
	// compute its new liveBefore, see if it has changed (it can only
	// get bigger)
	set<unsigned> *newLiveBefore = computeLiveBefore(bb);
	set<unsigned> *oldLiveBefore = liveBeforeMap[bb];
	if (newLiveBefore->size() > oldLiveBefore->size()) {
	  // update the liveBefore map and put all preds of bb on worklist
	  liveBeforeMap.erase(bb);
	  liveBeforeMap[bb] = newLiveBefore;
	  for (MachineBasicBlock::pred_iterator PI = bb->pred_begin(),
		 E = bb->pred_end();
	       PI != E; PI++) {
	    worklist.insert(*PI);
	  }
	}
      }
      argPregSet = liveBeforeMap[firstBB];
    }
    
    //**********************************************************************
    // analyzeBasicBlocksRDefs
    //**********************************************************************
    void analyzeBasicBlocksRDefs(MachineFunction &Fn) {
      // iterate over all basic blocks bb computing
      //    bb.gen = for each reg v defined in bb at inst: the RDfact
      //             (v, inst)
      //    bb.kill = all dataflow facts with reg v
      // also put bb on the worklist
      
      set<MachineBasicBlock *> worklist;
      for (MachineFunction::iterator MFIt = Fn.begin(), MFendIt = Fn.end();
	   MFIt != MFendIt; MFIt++) {
	RDbeforeMap[MFIt] = new set<RDfact *>();
	RDafterMap[MFIt] = new set<RDfact *>();
	RDgenMap[MFIt] = getRDgen(MFIt);
	RDkillMap[MFIt] = getRDkill(MFIt);
	worklist.insert(MFIt);
      }
      
      // while the worklist is not empty {
      //   remove one basic block bb
      //   compute new bb.RDbefore = union of RDafter's of all preds
      //   replace old RDbefore with new one
      //   compute new bb.RDafter = (bb.RDbefore - bb.RDkill) union
      //                              bb.RDgen
      //   if bb.RDafter changed {
      //      replace old RDbefore with new one
      //      add all of bb's succs to the worklist
      //   }
      // }
      while (! worklist.empty()) {
	// remove one basic block and compute its new RDbefore set
	set<MachineBasicBlock *>::iterator oneBB = worklist.begin();
	MachineBasicBlock *bb = *oneBB;
	worklist.erase(bb);
	
	set<RDfact *> *newRDbefore = computeRDbefore(bb);
	
	// update the RDbefore map
	RDbeforeMap.erase(bb);
	RDbeforeMap[bb] = newRDbefore;
	// compute its new RDafter, see if it has changed (it can only
	// get bigger)
	set<RDfact *> *newRDafter = computeRDafter(bb);
	set<RDfact *> *oldRDafter = RDafterMap[bb];
	if (newRDafter->size() > oldRDafter->size()) {
	  // update the RDafter map and put all succs of bb on worklist
	  RDafterMap.erase(bb);
	  RDafterMap[bb] = newRDafter;
	  for (MachineBasicBlock::succ_iterator PI = bb->succ_begin(),
		 E = bb->succ_end();
	       PI != E; PI++) {
	    worklist.insert(*PI);
	  }
	}
      }
    }
    
    // **********************************************************************
    // computeLiveBefore
    //
    // given: bb          ptr to a MachineBasicBlock 
    //
    // do:    compute and return bb's current LiveBefore set:
    //          (bb.liveAfter - bb.kill) union bb.gen
    // **********************************************************************
    set<unsigned> *computeLiveBefore(MachineBasicBlock *bb) {
      return regSetUnion(regSetSubtract(liveAfterMap[bb],
					liveVarsKillMap[bb]
					),
			 liveVarsGenMap[bb]
			 );
    }
    
    
    // **********************************************************************
    // computeLiveAfter
    //
    // given: bb  ptr to a MachineBasicBlock 
    //
    // do:    compute and return bb's current LiveAfter set: the union
    //        of the LiveBefore sets of all of bb's CFG successors
    // **********************************************************************
    set<unsigned> *computeLiveAfter(MachineBasicBlock *bb) {
      set<unsigned> *result = new set<unsigned>();
      for (MachineBasicBlock::succ_iterator SI = bb->succ_begin();
	   SI != bb->succ_end(); SI++) {
	MachineBasicBlock *oneSucc = *SI;
	result = regSetUnion(result, liveBeforeMap[oneSucc]);
      }
      
      return result;
    }
    
    
    // **********************************************************************
    // computeRDbefore
    //
    // given: bb  ptr to a MachineBasicBlock 
    //
    // do:    compute and return bb's current RDbefore set: the union
    //        of the RDafter sets of all of bb's CFG preds, except if
    //        bb is *first*, then a set of RDfacts for the pregs that
    //        are used to pass in args
    // **********************************************************************
    set<RDfact *> *computeRDbefore(MachineBasicBlock *bb) {
      set<RDfact *> *result = new set<RDfact *>();
      if (bb == firstBB) {
	for (std::set<unsigned>::iterator IT = argPregSet->begin();
	     IT != argPregSet->end();
	     IT++) {
	  result->insert(new RDfact(*IT, 0));
	}
      } else {
	for (MachineBasicBlock::pred_iterator SI = bb->pred_begin();
	     SI != bb->pred_end(); SI++) {
	  MachineBasicBlock *onePred = *SI;
	  result = RDsetUnion(result, RDafterMap[onePred]);
	}
	if (result->size() > RDfactSet.size()) {
	  std::cerr << "INTERNAL ERROR, bad new RDfact before set\n";
	  printRDSet(result);
	  std::cerr << "\n";
	  exit(1);
	}
      }
      return result;
    }
    
    // **********************************************************************
    // computeRDafter
    //
    // given: bb          ptr to a MachineBasicBlock 
    //
    // do:    compute and return bb's current RDafter set:
    //          (bb.RDbefore - bb.kill) union bb.gen
    // **********************************************************************
    set<RDfact *> *computeRDafter(MachineBasicBlock *bb) {
      return RDsetUnion(RDsetSubtract(RDbeforeMap[bb],
				      RDkillMap[bb]
				      ),
			RDgenMap[bb]
			);
    }
    
    
    
    // **********************************************************************
    // regSetUnion
    //
    // given: S1, S2          ptrs to sets of regs
    // do:    return a ptr to (*S1 union *S2)
    // **********************************************************************
    set<unsigned> *regSetUnion(set<unsigned> *S1, set<unsigned> *S2) {
      set<unsigned> *result = new set<unsigned>();
      // iterate over S1
      for (set<unsigned>::iterator oneRegPtr = S1->begin();
	   oneRegPtr != S1->end();
	   oneRegPtr++) {
	result->insert(*oneRegPtr);
      }
      
      // iterate over S2
      for (set<unsigned>::iterator oneRegPtr = S2->begin();
	   oneRegPtr != S2->end();
	   oneRegPtr++) {
	result->insert(*oneRegPtr);
      }
      
      return result;
    }
    
    // **********************************************************************
    // RDsetUnion
    //
    // given: S1, S2          ptrs to sets of ptrs to RDfacts
    // do:    return a ptr to (*S1 union *S2)
    // **********************************************************************
    set<RDfact *> *RDsetUnion(set<RDfact *> *S1, set<RDfact *> *S2) {
      set<RDfact *> *result = new set<RDfact *>();
      // iterate over S1
      for (set<RDfact *>::iterator oneRDfact = S1->begin();
	   oneRDfact != S1->end();
	   oneRDfact++) {
	result->insert(*oneRDfact);
      }
      
      // iterate over S2
      for (set<RDfact *>::iterator oneRDfact = S2->begin();
	   oneRDfact != S2->end();
	   oneRDfact++) {
	result->insert(*oneRDfact);
      }
      
      return result;
    }
    
    
    // **********************************************************************
    // regSetSubtract
    //
    // given: S1, S2          ptrs to sets of regs
    // do:    return a ptr to (*S1 - *S2)
    //
    // **********************************************************************
    set<unsigned> *regSetSubtract(set<unsigned> *S1, set<unsigned> *S2) {
      set<unsigned> *result = new set<unsigned>();
      // iterate over S1; for each element, if it is NOT in S2, then
      // add it to the result
      for (set<unsigned>::iterator S1RegPtr = S1->begin();
	   S1RegPtr != S1->end();
	   S1RegPtr++) {
	if (S2->count(*S1RegPtr) == 0) {
	  result->insert(*S1RegPtr);
	}
      }
      
      return result;
    }
    
    // **********************************************************************
    // RDsetSubtract
    //
    // given: S1, S2          ptrs to sets of RDfact ptrs
    // do:    return a ptr to (*S1 - *S2)
    //
    // **********************************************************************
    set<RDfact *> *RDsetSubtract(set<RDfact *> *S1, set<RDfact *> *S2) {
      set<RDfact *> *result = new set<RDfact *>();
      // iterate over S1; for each element, if it is NOT in S2, then
      // add it to the result
      for (std::set<RDfact *>::iterator S1It = S1->begin();
	   S1It != S1->end();
	   S1It++) {
	RDfact *fact1 = *S1It;
	bool found = false;
	std::set<RDfact *>::iterator S2It = S2->begin();
	while (!found && S2It != S2->end()) {
	  RDfact *fact2 = *S2It;
	  if (fact1->getReg() == fact2->getReg() &&
	      fact1->getInstr() == fact2->getInstr()) found = true;
	  S2It++;
	}
	if (!found) result->insert(fact1);
      } // end iterate over S1
      return result;
    }

    //**********************************************************************
    // analyzeInstructionsLiveVars
    //
    // do live-var analysis at the instruction level:
    //   iterate over all basic blocks
    //   for each, iterate backwards over instructions, propagating
    //             live-var info:
    //     for each instruction inst
    //             live-before = (live-after - kill) union gen
    //     where kill is the defined reg of inst (if any) and
    //           gen is all reg-use operands of inst
    //**********************************************************************
    void analyzeInstructionsLiveVars(MachineFunction &Fn) {
      for (MachineFunction::iterator bb = Fn.begin(), bbe = Fn.end(); 
	   bb != bbe; bb++) {
	// no reverse iterator and recursion doesn't work,
	// so create vector of instructions for backward traversal
	vector<MachineInstr *> instVector;
	for (MachineBasicBlock::iterator inIt = bb->begin(); inIt != bb->end(); inIt++) {
	  instVector.push_back(inIt);
	}
	
	liveForInstr(instVector, liveAfterMap[bb]);
      }
    }
    
    //**********************************************************************
    // analyzeInstructionsRDefs
    //
    // given reaching-defs before and after facts for basic block,
    // compute before/after facts for each instruction in each basic block
    //
    // for one instruction: RDafter = (RDbefore - kill) union gen
    // where kill is all dataflow facts with the regs that are defined
    // by this instruction (if any), and gen is the set of facts (reg, inst)
    // for all regs defined by this instruction (if any)
    //**********************************************************************
    void analyzeInstructionsRDefs(MachineFunction &Fn) {
      // iterate over all basic blocks in this function
      for (MachineFunction::iterator bb = Fn.begin(), bbe = Fn.end(); 
	   bb != bbe; bb++) {
	set<RDfact *> *RDbefore = RDbeforeMap[bb];
	// iterate over all instructions in this basic block
	for (MachineBasicBlock::iterator inIt = bb->begin();
	     inIt != bb->end();
	     inIt++) {
	  insRDbeforeMap[inIt] = RDbefore;
	  set<RDfact *> *kill = new set<RDfact *>();
	  set<RDfact *> *gen = new set<RDfact *>();
	  set<unsigned> *regDefs = getOneInstrRegDefs(inIt);
	  // if at least one reg was defined
	  // then compute gen and kill sets for this instruction
	  if (regDefs->size() > 0) {
	    for (set<unsigned>::iterator regIt = regDefs->begin();
		 regIt != regDefs->end(); regIt++) {
	      unsigned oneDef = *regIt;
	      gen->insert(new RDfact(oneDef, inIt));
	      // iterate over all RDfacts, see which are killed
	      for (set<RDfact *>::iterator IT = RDfactSet.begin();
		   IT != RDfactSet.end(); IT++) {
		RDfact *oneRDfact = *IT;
		unsigned oneReg = oneRDfact->getReg();
		if (oneReg == oneDef) {
		  kill->insert(oneRDfact);
		}
	      } // end iterate over all RDfacts to compute kill
	    } // end iterate over set of regs defined by one instruction

	    // we've now defined the gen and kill sets so we can
	    // compute the "after" fact for this instruction
	    set<RDfact *> *RDafter = RDsetUnion(RDsetSubtract(RDbefore, kill),
						gen);
	    insRDafterMap[inIt] = RDafter;
	    RDbefore = RDafter;
	  } else {
	    // this instruction doesn't define any reg
	    insRDafterMap[inIt] = RDbefore;
	  }
	} // end iterate over all instructions in 1 basic block
      } // end iterate over all basic blocks
    }
    
    // **********************************************************************
    // getUpwardsExposedUses
    //
    // given: bb      ptr to a basic block
    // do:    return a ptr to the set of regs that are used before
    //        being defined in bb
    // **********************************************************************
    set<unsigned> *getUpwardsExposedUses(MachineBasicBlock *bb) {
      set<unsigned> *result = new set<unsigned>();
      set<unsigned> *defs = new set<unsigned>();
      for (MachineBasicBlock::iterator instruct = bb->begin(),
	     instructEnd = bb->end(); instruct != instructEnd; instruct++) {
	set<unsigned> *uses = getOneInstrRegUses(instruct);
	set<unsigned> *upUses = regSetSubtract(uses, defs);
	result = regSetUnion(result, upUses);
	set<unsigned> *defSet = getOneInstrRegDefs(instruct);
	for (set<unsigned>::iterator IT = defSet->begin();
	     IT != defSet->end(); IT++) {
	  unsigned oneDef = *IT;
	  defs->insert(oneDef);
	}
      } // end iterate over all instrutions in this basic block
      
      return result;
    }
    
    
    // **********************************************************************
    // getRDgen
    //
    // given: bb      ptr to a basic block
    // do:    return a set of reaching-def facts: the ones that occur in bb
    // **********************************************************************
    set<RDfact *> *getRDgen(MachineBasicBlock *bb) {
      set<RDfact *> *result = new set<RDfact *>();
      for (MachineBasicBlock::iterator instruct = bb->begin(),
	     instructEnd = bb->end(); instruct != instructEnd; instruct++) {
	set<unsigned> *defSet = getOneInstrRegDefs(instruct);
	for (set<unsigned>::iterator IT = defSet->begin();
	     IT != defSet->end(); IT++) {
	  unsigned oneDef = *IT;
	  result->insert(new RDfact(oneDef, instruct));
	}
      } // end iterate over all instructions in this basic block
      
      return result;
    }
    
    // **********************************************************************
    // getRDkill
    //
    // given: bb      ptr to a basic block
    // do:    return a set of reaching-def facts: the ones whose reg
    //        component is defined in bb
    // **********************************************************************
    set<RDfact *> *getRDkill(MachineBasicBlock *bb) {
      set<RDfact *> *result = new set<RDfact *>();
      for (MachineBasicBlock::iterator instruct = bb->begin(), instructEnd = bb->end(); instruct != instructEnd; instruct++) {
	set<unsigned> *defSet = getOneInstrRegDefs(instruct);
	for (set<unsigned>::iterator IT = defSet->begin(); IT != defSet->end(); IT++) {
	  unsigned oneDef = *IT;
	  for (set<RDfact *>::iterator IT = RDfactSet.begin(); IT != RDfactSet.end(); IT++) {
	    RDfact *oneRDfact = *IT;
	    unsigned oneReg = oneRDfact->getReg();
	    if (oneReg == oneDef) {
	      result->insert(oneRDfact);
	    }
	  } // end iterate over all RDfacts in the whole fn
	} // end iterate over all defs in this instruction
      } // end iterate over all instructions in this basic block
      
      return result;
    }
    
    //**********************************************************************
    // getOneInstrRegUses
    //
    // return the set of registers (virtual or physical) used by the
    // given instruction
    //**********************************************************************
    set<unsigned> *getOneInstrRegUses(MachineInstr *instruct) {
      set<unsigned> *result = new set<unsigned>();
      unsigned numOperands = instruct->getNumOperands();
      for (unsigned n=0; n<numOperands; n++) {
	MachineOperand MOp = instruct->getOperand(n);
	if (MOp.isReg() && MOp.getReg() && MOp.isUse()) {
	  unsigned reg = MOp.getReg();
	  result->insert(reg);
	}
      } // end for each operand of current instruction
      return result;
    }
    
    //**********************************************************************
    // getOneInstrRegDefs
    //
    // return a ptr to a set of the registers defined by this instruction
    //**********************************************************************
    set<unsigned> *getOneInstrRegDefs(MachineInstr *instruct) {
      set<unsigned> *result = new set<unsigned>();
      unsigned numOperands = instruct->getNumOperands();
      for (unsigned n=0; n<numOperands; n++) {
	MachineOperand MOp = instruct->getOperand(n);
	if (MOp.isReg() && MOp.getReg() && MOp.isDef()) {
	  unsigned reg = MOp.getReg();
	  result->insert(reg);
	}
      } // end for each operand of current instruction
      return result;
    }
    
    // **********************************************************************
    // getAllDefs
    //
    // given: bb      ptr to a basic block
    // do:    return the set of regs that are defined in bb
    // **********************************************************************
    set<unsigned> *getAllDefs(MachineBasicBlock *bb) {
      set<unsigned> *result = new set<unsigned>();
      
      // iterate over all instructions in bb
      //   for each operand that is a non-zero reg:
      //     if it is a def then add it to the result set
      // return result
      // 
      for (MachineBasicBlock::iterator instruct = bb->begin(),
	     instructEnd = bb->end(); instruct != instructEnd; instruct++) {
	unsigned numOperands = instruct->getNumOperands();
	for (unsigned n=0; n<numOperands; n++) {
	  MachineOperand MOp = instruct->getOperand(n);
	  if (MOp.isReg() && MOp.getReg() && MOp.isDef()) {
	    result->insert(MOp.getReg());
	  }
	} // end for each operand of current instruction
      } // end iterate over all instrutions in this basic block
      return result;
    }
    
    // **********************************************************************
    // liveForInstr
    //
    // given: instVector vector of ptrs to Instructions for one basic block
    //        liveAfter  live after set for the *last* instruction in the block
    //
    // do:    compute and set liveAfter and liveBefore for each instruction
    //        liveAfter = liveBefore of next instruction
    //        liveBefore = (liveAfter - kill) union gen
    // **********************************************************************
    void liveForInstr(vector<MachineInstr *>instVector,
		      set<unsigned> *liveAfter) {
      while (instVector.size() > 0) {
	MachineInstr *oneInstr = instVector.back();
	instVector.pop_back();
	insLiveAfterMap[oneInstr] = liveAfter;
	
	// create liveBefore for this instruction
	// (which is also liveAfter for the previous one in the block)
	//   remove the reg defined here (if any) from the set
	//   then add all used reg operands
	
	set<unsigned> *liveBefore;
	set<unsigned> *gen = getOneInstrRegUses(oneInstr);
	set<unsigned> *kill = getOneInstrRegDefs(oneInstr);
	if (kill->size() != 0) {
	  liveBefore = regSetUnion(regSetSubtract(liveAfter, kill), gen);
	} else {
	  liveBefore = regSetUnion(liveAfter, gen);
	}
	
	// add this instruction's liveBefore set to the map
	// and prepare for the next iteration of the loop
	insLiveBeforeMap[oneInstr] = liveBefore;
	liveAfter = liveBefore;
      } // end while
    }
    
    //**********************************************************************
    // getNumRegClasses
    //
    // set field numRegClasses to value for this machine arch
    //**********************************************************************
    void getNumRegClasses(MachineFunction &Fn) {
      numRegClasses = Fn.getTarget().getRegisterInfo()->getNumRegClasses();
    }
    
    // **********************************************************************
    // printInstructions
    // **********************************************************************
    void printInstructions(MachineFunction &F) {
      std::cerr << "\nMACHINE INSTRUCTIONS\n";
      // iterate over all basic blocks
      for (MachineFunction::iterator bb = F.begin(); bb != F.end(); bb++) {
	cerr << "Basic Block " << bb->getName().str() << "\n";
	// iterate over instructions, printing each
	for (MachineBasicBlock::iterator inIt = bb->begin(), ine = bb->end();
	     inIt != ine; inIt++) {
	  MachineInstr *oneI = inIt;
	  cerr << "%" << InstrToNumMap[oneI] << ": ";
	  oneI->dump();
	}
      }
      std::cerr << "\n";
    }

    // **********************************************************************
    // printLiveResults
    //
    // given: MachineFunction F
    //
    // do:    for each basic block in F {
    //           print fn name, bb number, liveBefore and After sets
    //           for each instruction, print instruction num, liveBefore and
    //               liveAfter
    //        }
    // 
    // **********************************************************************
    void printLiveResults(MachineFunction &F) {
      std::cerr << "\nLIVE VARS\n";
      
      // iterate over all basic blocks
      for (MachineFunction::iterator bb = F.begin(); bb != F.end(); bb++) {
	// print name of basic block
	std::cerr << "\nBASIC BLOCK " << bb->getName().str() << "\n";
	// print live before and after sets
	std::cerr << "  L-Before: ";
	printRegSet(liveBeforeMap[bb]);
	std::cerr << "  L-After: ";
	printRegSet(liveAfterMap[bb]);
	
	// iterate over instructions, printing each live set
	// (note that liveAfter of one instruction is liveBefore of the next one)
	for (MachineBasicBlock::iterator inIt = bb->begin(), ine = bb->end();
	     inIt != ine; inIt++) {
	  std::cerr << "%" << InstrToNumMap[inIt] << ": ";
	  std::cerr << "\tL-Before: ";
	  printRegSet(insLiveBeforeMap[inIt]);
	  std::cerr << "\tL-After: ";
	  printRegSet(insLiveAfterMap[inIt]);
	}
      }
    }
    
    // **********************************************************************
    // printRDResults
    //
    // given: MachineFunction F
    //
    // do:    for each basic block in F {
    //           print fn name, bb number, RDBefore and After sets
    //           for each instruction, print instruction num, RDBefore and
    //               RDAfter
    //        }
    // 
    // **********************************************************************
    void printRDResults(MachineFunction &F) {
      std::cerr << "\nREACHING DEFS\n";
      
      // iterate over all basic blocks
      for (MachineFunction::iterator bb = F.begin(); bb != F.end(); bb++) {
	// print name of basic block
	std::cerr << "BASIC BLOCK " << bb->getName().str() << "\n";
	// print RD before and after sets
	std::cerr << "  RD-Before: ";
	printRDSet(RDbeforeMap[bb]);
	std::cerr << "  RD-After: ";
	printRDSet(RDafterMap[bb]);
	
	// iterate over instructions, printing each RD set
	// (note that RDAfter of one instruction is RDBefore of the next one)
	for (MachineBasicBlock::iterator inIt = bb->begin(), ine = bb->end();
	     inIt != ine; inIt++) {
	  std::cerr << "%" << InstrToNumMap[inIt] << ": ";
	  std::cerr << "\tRD-Before: ";
	  printRDSet(insRDbeforeMap[inIt]);
	  std::cerr << "\tRD-After: ";
	  printRDSet(insRDafterMap[inIt]);
	  std::cerr << "\n";
	}
      }
    }
    
    // **********************************************************************
    // printRegSet
    //
    // given: S      ptr to set of regs (unsigned)
    // do:    print the set
    // ********************************************************************
    void printRegSet(set<unsigned> *S) {
      std::cerr << "{";
      for (set<unsigned>::iterator IT = S->begin(); IT != S->end(); IT++) {
	unsigned reg = *IT;
	std::cerr << " ";
	printReg(reg);
      }
      std::cerr << " }\n";
    }
      
    // **********************************************************************
    // printReg
    //
    // given: unsigned           vreg or preg
    //
    // do: print R for physical, % for virtual, followed by reg number
    //
    // NOTE: To print virtual-reg index use:
    //           TargetRegisterInfo::virtReg2Index(reg)
    // **********************************************************************
    void printReg(unsigned reg) {
      if (TargetRegisterInfo::isPhysicalRegister(reg)) {
	std::cerr << "R" << reg;
      } else {
	std::cerr << "%" << TargetRegisterInfo::virtReg2Index(reg);
      }
    }
    // **********************************************************************
    // printRDSet
    //
    // given: S      ptr to set of RDfact
    // do:    print the set
    // **********************************************************************
    void printRDSet(set<RDfact *> *S) {
      std::cerr << "{";
      for (set<RDfact *>::iterator IT = S->begin(); IT != S->end(); IT++) {
	RDfact *oneRDfact = *IT;
	MachineInstr *oneIns = oneRDfact->getInstr();
	std::cerr << "(";
	printReg(oneRDfact->getReg());
	std::cerr << ", %" << InstrToNumMap[oneIns] << ") ";
      }
      std::cerr << " }\n";
    }
    
    //**********************************************************************
    // printRegSet
    //**********************************************************************
    void printRegSet(set<unsigned> S) {
      for (set<unsigned>::iterator IT = S.begin(); IT != S.end(); IT++) {
	unsigned reg = *IT;
	std::cerr << reg << " ";
      }
    }
    
    // **********************************************************************
    // update (global) RDfactSet by adding a fact of the form (p, 0)
    // for each preg p in (global) argPregSet
    // **********************************************************************
    void addArgPregsToRDfactSet() {
      for (std::set<unsigned>::iterator IT = argPregSet->begin();
	   IT != argPregSet->end();
	   IT++) {
	RDfactSet.insert(new RDfact(*IT, 0));
      }
    }

  };
  
  // The library-inclusion mechanism requires the following:
  char Gcra::ID = 0;
  
  FunctionPass *createGcra() { return new Gcra(); }
  
  static RegisterRegAlloc register_gcra("gc",
					"graph-coloring register allocator",
					createGcra);
}
