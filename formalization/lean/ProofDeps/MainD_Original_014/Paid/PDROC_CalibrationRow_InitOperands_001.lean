module

public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDROC_CalibrationRow_Init_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- The real one-op center assignment retains the same caller budget;
all other registers/heap/output values keep their previous bounds. -/
theorem initCenter_prefix_safe (input : List Cell) (before : State) (budget : ℕ)
    (safe : SafeBits before budget) (oneBits : (Cell.rational 1).bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input (basicBlock .initCenter).body before budget :=
  PrefixSafe.constant input before budget .value (.rational 1) safe oneBits pcBits

/-- All five actual initCell prefixes: load the real level, compare the
real cursor, then write Rat0. Header6 and arbitrary scratch never acquire
an invented parameter-only bound. No bound grows with the row width. -/
theorem initCell_prefix_safe (input : List Cell) (before : State)
    (base level cursor budget : ℕ) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (live : base+5∈before.live)
    (levelValue : before.heap (base+5)=.natural level)
    (index : before.register .index=.natural cursor)
    (addressBits : 1+natBits (base+5)≤budget)
    (zeroNatBits : (Cell.natural 0).bits≤budget) (oneNatBits : (Cell.natural 1).bits≤budget)
    (zeroRatBits : (Cell.rational 0).bits≤budget) (pcBits : natBits (before.pc+5)≤budget) :
    PrefixSafe input (basicBlock .initCell).body before budget := by
  let loaded := loadSlotResult before base 5 .total
  let compare : Instruction := .natCompare .equal .flag .index .total
  let compared := ({loaded with pc:=loaded.pc+1}).set .flag (.natural (if cursor=level then 1 else 0))
  have loadRun : linearExecute input (loadSlot 5 .total) before=some loaded :=
    loadSlot_execute input before base 5 .total fresh live
  have loadSafe := PrefixSafe.loadSlot input before base 5 budget .total safe fresh live addressBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+5)).trans pcBits)
  have comparedRun : linearExecute input [compare] loaded=some compared := by
    simp [compare,linearExecute,Instruction.execute,loaded,loadSlotResult,State.set,
      Cell.nat?,Comparison.nat,index,levelValue,compared]
  have comparedSafe : PrefixSafe input [compare] loaded budget :=
    PrefixSafe.natCompare input loaded budget .equal .flag .index .total cursor level
      (loadSafe.final loadRun)
      (by simp [loaded,loadSlotResult,index]) (by simp [loaded,loadSlotResult,levelValue])
      zeroNatBits oneNatBits
      (by simpa only [loaded,loadSlotResult] using
        ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+5)).trans pcBits))
  have constantSafe : PrefixSafe input [.constant .value (.rational 0)] compared budget :=
    PrefixSafe.constant input compared budget .value (.rational 0) (comparedSafe.final comparedRun) zeroRatBits
      (by simpa only [compared,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input [compare] [.constant .value (.rational 0)]
    loaded compared budget comparedRun comparedSafe constantSafe
  change PrefixSafe input (loadSlot 5 .total++[compare,.constant .value (.rational 0)]) before budget
  exact PrefixSafe.append input (loadSlot 5 .total) [compare,.constant .value (.rational 0)]
    before loaded budget loadRun loadSafe suffix

end PDROC.CalibrationRow.Operand
