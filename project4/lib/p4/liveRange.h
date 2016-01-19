#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
//#include "llvm/CodeGen/VirtRegMap.h"
//#include "llvm/Target/TargetInstrDesc.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Compiler.h"
#include "llvm/ADT/Statistic.h"


class liveRange {
public:

  // constructor
  liveRange(unsigned reg, std::set<MachineInstr*> range);
  unsigned getReg();
  std::set<MachineInstr*> getLiveSet();

private:
  unsigned myReg;
  std::set<MachineInstr*> myLiveRange;

};
