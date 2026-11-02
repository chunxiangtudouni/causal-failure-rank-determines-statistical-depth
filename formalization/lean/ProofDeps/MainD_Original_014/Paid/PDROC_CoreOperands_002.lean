module

public import Paid.PDROC_CoreOperands_001
public import Paid.RootD27Core_HeapArguments_013
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CoreOperands

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDROC.CalibrationRow.Operand

/-- Every real prefix of the frozen thirteen-op live-heap argument code.
The first instruction really establishes fresh0 before the three loads;
all untouched scratch/heap/output remain covered by actual caller B. -/
theorem endpoint_heap_arguments_prefix_safe (input : List Cell) (before : State)
    (base cache returnPC budget : ℕ) (safe : SafeBits before budget)
    (live : ∀ slot<13,slot∈before.live) (small : 4≤budget)
    (baseBits : (Cell.natural base).bits≤budget) (cacheBits : (Cell.natural cache).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+13)≤budget) :
    PrefixSafe input (RootD27.Core.endpointHeapArgumentsCode base cache returnPC) before budget := by
  let start := ({before with pc:=before.pc+1}).set .fresh (.natural 0)
  let first := loadSlotResult start 0 7 .index
  let second := loadSlotResult first 0 2 .total
  let third := loadSlotResult second 0 4 .value
  let addressed := ({third with pc:=third.pc+1}).set .address (.natural cache)
  let returned := ({addressed with pc:=addressed.pc+1}).set .old (.natural returnPC)
  let final := ({returned with pc:=returned.pc+1}).set .fresh (.natural base)
  have zeroBits : (Cell.natural 0).bits≤budget := (show (Cell.natural 0).bits≤4 by decide).trans small
  have startSafe : SafeBits start budget :=
    (safe.withPC _ ((PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+13)).trans pcBits)).set _ _ zeroBits
  have startFresh : start.register .fresh=.natural 0 := by simp [start,State.set]
  have firstRun : linearExecute input (loadSlot 7 .index) start=some first :=
    loadSlot_execute input start 0 7 .index startFresh (live 7 (by decide))
  have firstSafe := PrefixSafe.loadSlot input start 0 7 budget .index startSafe startFresh (live 7 (by decide))
    ((show 1+natBits (0+7)≤4 by decide).trans small)
    (by simpa only [start,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+13)).trans pcBits))
  have firstFresh : first.register .fresh=.natural 0 := by simp [first,loadSlotResult,start,State.set]
  have secondRun : linearExecute input (loadSlot 2 .total) first=some second :=
    loadSlot_execute input first 0 2 .total firstFresh (live 2 (by decide))
  have secondSafe := PrefixSafe.loadSlot input first 0 2 budget .total (firstSafe.final firstRun)
    firstFresh (live 2 (by decide)) ((show 1+natBits (0+2)≤4 by decide).trans small)
    (by simpa only [first,start,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+7≤before.pc+13)).trans pcBits))
  have secondFresh : second.register .fresh=.natural 0 := by
    simp [second,first,loadSlotResult,start,State.set]
  have thirdRun : linearExecute input (loadSlot 4 .value) second=some third :=
    loadSlot_execute input second 0 4 .value secondFresh (live 4 (by decide))
  have thirdSafe := PrefixSafe.loadSlot input second 0 4 budget .value (secondSafe.final secondRun)
    secondFresh (live 4 (by decide)) ((show 1+natBits (0+4)≤4 by decide).trans small)
    (by simpa only [second,first,start,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+10≤before.pc+13)).trans pcBits))
  have addressedSafe : SafeBits addressed budget :=
    ((thirdSafe.final thirdRun).withPC _ (by
      simpa only [third,second,first,start,loadSlotResult,State.set,Nat.add_assoc] using
        ((PDROC.DataBits.natBits_mono (by omega : before.pc+11≤before.pc+13)).trans pcBits))).set _ _ cacheBits
  have returnedSafe : SafeBits returned budget :=
    (addressedSafe.withPC _ (by
      simpa only [addressed,third,second,first,start,loadSlotResult,State.set,Nat.add_assoc] using
        ((PDROC.DataBits.natBits_mono (by omega : before.pc+12≤before.pc+13)).trans pcBits))).set _ _ returnBits
  have finalSafe : SafeBits final budget :=
    (returnedSafe.withPC _ (by
      simpa only [returned,addressed,third,second,first,start,loadSlotResult,State.set,Nat.add_assoc] using pcBits)).set _ _ baseBits
  have tailSafe : PrefixSafe input
      [.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)] third budget := by
    apply PrefixSafe.cons input _ _ third addressed budget rfl (thirdSafe.final thirdRun)
    apply PrefixSafe.cons input _ _ addressed returned budget rfl addressedSafe
    apply PrefixSafe.cons input _ [] returned final budget rfl returnedSafe
    exact PrefixSafe.nil input final budget finalSafe
  have loadThird := PrefixSafe.append input (loadSlot 4 .value)
    [.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)]
    second third budget thirdRun thirdSafe tailSafe
  have loadSecond := PrefixSafe.append input (loadSlot 2 .total)
    (loadSlot 4 .value++[.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)])
    first second budget secondRun secondSafe loadThird
  have loadFirst := PrefixSafe.append input (loadSlot 7 .index)
    (loadSlot 2 .total++loadSlot 4 .value++[.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)])
    start first budget firstRun firstSafe loadSecond
  change PrefixSafe input (.constant .fresh (.natural 0)::
    (loadSlot 7 .index++loadSlot 2 .total++loadSlot 4 .value++
      [.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)])) before budget
  exact PrefixSafe.cons input _ _ before start budget rfl safe loadFirst

end PDROC.CoreOperands
