module

public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_HeaderOps_027
public import Paid.PDROC_CalibrationRow_ControlOperands_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem sumStart_prefix_safe (input : List Cell) (before : State) (base budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (zeroNat : (Cell.natural 0).bits≤budget) (zeroRat : (Cell.rational 0).bits≤budget)
    (address7 : 1+natBits (base+7)≤budget) (address11 : 1+natBits (base+11)≤budget)
    (pcBits : natBits (before.pc+8)≤budget) :
    PrefixSafe input (basicBlock .sumStart).body before budget := by
  let first := constantSlotResult before base 11 (.rational 0)
  have firstRun : linearExecute input (constantSlot 11 (.rational 0)) before=some first :=
    constantSlot_execute input before base 11 (.rational 0) fresh
  have firstSafe := constantSlot_sameBudget input before base 11 budget (.rational 0) safe fresh zeroRat address11
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+8)).trans pcBits)
  have firstFresh : first.register .fresh=.natural base :=
    (constantSlot_fresh before base 11 (.rational 0)).trans fresh
  have secondSafe := constantSlot_sameBudget input first base 7 budget (.natural 0)
    (firstSafe.final firstRun) firstFresh zeroNat address7
    (by simpa only [first,constantSlotResult,storeSlotResult,State.set,Nat.add_assoc] using pcBits)
  exact PrefixSafe.append input (constantSlot 11 (.rational 0)) (constantSlot 7 (.natural 0))
    before first budget firstRun firstSafe secondSafe

/-- Real sum initialization, both four-op stores, actual control jump,
and every original complete-state operand bit on the same fetched trace. -/
theorem sumStart_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (position : before.pc=labelAddress origin .sumStart)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (zeroNat : (Cell.natural 0).bits≤budget) (zeroRat : (Cell.rational 0).bits≤budget)
    (address7 : 1+natBits (base+7)≤budget) (address11 : 1+natBits (base+11)≤budget)
    (pcBits : natBits (before.pc+8)≤budget) (targets : ∀ label,natBits (labelAddress origin label)≤budget) :
    BitSegment origin input before {(sumStartResult before base) with pc:=labelAddress origin .sumGate} 150 budget := by
  let middle := sumStartResult before base
  let after : State := {middle with pc:=labelAddress origin .sumGate}
  have body : linearExecute input (basicBlock .sumStart).body before=some middle := sumStart_execute input before base fresh
  have control : (controlInstruction origin (basicBlock .sumStart).control).execute input middle=some after := rfl
  have prefixes := sumStart_prefix_safe input before base budget safe fresh zeroNat zeroRat address7 address11 pcBits
  have finalSafe := control_safe origin (basicBlock .sumStart).control input middle after budget
    (prefixes.final body) targets control
  have actual := BitSegment.ofBlock origin .sumStart input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) finalSafe
  exact actual

end PDLower.CalibrationCompute
