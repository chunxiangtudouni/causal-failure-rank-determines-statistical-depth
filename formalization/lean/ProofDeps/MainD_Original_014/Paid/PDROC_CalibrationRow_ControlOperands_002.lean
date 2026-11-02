module

public import Paid.PDROC_CalibrationRow_ControlOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Proof-side factorization of the LAST twelve original stepNext
instructions. Both pointer words are loaded before either is overwritten;
all values keep the same caller B, even during the temporary alias. -/
def swapTailCode : List Instruction :=
  loadSlot 9 .old++loadSlot 10 .total++storeSlot 9 .total++storeSlot 10 .old

theorem swapTail_prefix_safe (input : List Cell) (before : State) (base budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (readLive : base+9∈before.live) (writeLive : base+10∈before.live)
    (readBits : 1+natBits (base+9)≤budget) (writeBits : 1+natBits (base+10)≤budget)
    (pcBits : natBits (before.pc+12)≤budget) :
    PrefixSafe input swapTailCode before budget := by
  let readLoaded := loadSlotResult before base 9 .old
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  let readStored := storeSlotResult writeLoaded base 9 .total
  have readFresh : readLoaded.register .fresh=.natural base := by
    simpa [readLoaded,loadSlotResult] using fresh
  have writeFresh : writeLoaded.register .fresh=.natural base := by
    simpa [writeLoaded,loadSlotResult] using readFresh
  have storedFresh : readStored.register .fresh=.natural base := by
    simpa [readStored,storeSlotResult] using writeFresh
  have readRun : linearExecute input (loadSlot 9 .old) before=some readLoaded :=
    loadSlot_execute input before base 9 .old fresh readLive
  have readSafe := PrefixSafe.loadSlot input before base 9 budget .old safe fresh readLive readBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+12)).trans pcBits)
  have writeRun : linearExecute input (loadSlot 10 .total) readLoaded=some writeLoaded :=
    loadSlot_execute input readLoaded base 10 .total readFresh writeLive
  have writeSafe := PrefixSafe.loadSlot input readLoaded base 10 budget .total (readSafe.final readRun)
    readFresh writeLive writeBits (by simpa only [readLoaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+6≤before.pc+12)).trans pcBits))
  have storeRun : linearExecute input (storeSlot 9 .total) writeLoaded=some readStored :=
    storeSlot_execute input writeLoaded base 9 .total writeFresh (by decide)
  have storeSafe := PrefixSafe.storeSlot input writeLoaded base 9 budget .total (writeSafe.final writeRun)
    writeFresh (by decide) readBits
    (by simpa only [writeLoaded,readLoaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+9≤before.pc+12)).trans pcBits))
  have lastSafe := PrefixSafe.storeSlot input readStored base 10 budget .old (storeSafe.final storeRun)
    storedFresh (by decide) writeBits
    (by simpa only [readStored,writeLoaded,readLoaded,loadSlotResult,storeSlotResult,State.set,Nat.add_assoc] using pcBits)
  have tailSafe := PrefixSafe.append input (storeSlot 9 .total) (storeSlot 10 .old)
    writeLoaded readStored budget storeRun storeSafe lastSafe
  have middleSafe := PrefixSafe.append input (loadSlot 10 .total) (storeSlot 9 .total++storeSlot 10 .old)
    readLoaded writeLoaded budget writeRun writeSafe tailSafe
  simpa only [swapTailCode,List.append_assoc] using
    PrefixSafe.append input (loadSlot 9 .old) (loadSlot 10 .total++(storeSlot 9 .total++storeSlot 10 .old))
      before readLoaded budget readRun readSafe middleSafe

end PDROC.CalibrationRow.Operand
