module

public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDROC_CalibrationRow_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- All seven genuine gate instructions retain exactly the same budget.
The two loaded words come from the caller's live header, followed by a
one-bit comparison flag. This also applies to the actual Q-clock gate. -/
theorem gate_prefix_safe (input : List Cell) (before : State)
    (base a b cursor bound budget : ℕ) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (aLive : base+a∈before.live) (bLive : base+b∈before.live)
    (cursorValue : before.heap (base+a)=.natural cursor)
    (boundValue : before.heap (base+b)=.natural bound)
    (aBits : 1+natBits (base+a)≤budget) (bBits : 1+natBits (base+b)≤budget)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+7)≤budget) :
    PrefixSafe input (gateCode a b) before budget := by
  let first := loadSlotResult before base a .index
  let second := loadSlotResult first base b .total
  let compare : Instruction := .natCompare .less .flag .index .total
  have firstRun : linearExecute input (loadSlot a .index) before=some first :=
    loadSlot_execute input before base a .index fresh aLive
  have firstSafe := PrefixSafe.loadSlot input before base a budget .index safe fresh aLive aBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+7)).trans pcBits)
  have firstFresh : first.register .fresh=.natural base := by simp [first,loadSlotResult,fresh]
  have secondRun : linearExecute input (loadSlot b .total) first=some second :=
    loadSlot_execute input first base b .total firstFresh bLive
  have secondSafe := PrefixSafe.loadSlot input first base b budget .total (firstSafe.final firstRun)
    firstFresh bLive bBits (by simpa only [first,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+6≤before.pc+7)).trans pcBits))
  have lastSafe : PrefixSafe input [compare] second budget :=
    PrefixSafe.natCompare input second budget .less .flag .index .total cursor bound
      (secondSafe.final secondRun)
      (by simp [second,first,loadSlotResult,cursorValue])
      (by simp [second,first,loadSlotResult,boundValue]) zeroBits oneBits
      (by simpa only [second,first,loadSlotResult,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input (loadSlot b .total) [compare] first second budget
    secondRun secondSafe lastSafe
  exact PrefixSafe.append input (loadSlot a .index) (loadSlot b .total++[compare])
    before first budget firstRun firstSafe suffix

/-- The original control instruction changes only PC. Indirect returns
use the actual old register, whose Cell bits are already in caller B. -/
theorem control_safe (origin : ℕ) (control : Control) (input : List Cell)
    (before after : State) (budget : ℕ) (safe : SafeBits before budget)
    (targets : ∀ label,natBits (labelAddress origin label)≤budget)
    (actual : (controlInstruction origin control).execute input before=some after) : SafeBits after budget := by
  cases control with
  | go label =>
      have same : {before with pc:=labelAddress origin label}=after := Option.some.inj actual
      subst after
      exact safe.withPC _ (targets label)
  | branch target zero nonzero =>
      cases value : before.register target with
      | natural n =>
          let counter := if n=0 then labelAddress origin zero else labelAddress origin nonzero
          have counterBits : natBits counter≤budget := by
            dsimp only [counter]
            split_ifs <;> apply targets
          have same : {before with pc:=counter}=after := Option.some.inj (by
            simpa [controlInstruction,Instruction.execute,value,Cell.nat?,counter] using actual)
          subst after
          exact safe.withPC _ counterBits
      | rational q => simp [controlInstruction,Instruction.execute,value,Cell.nat?] at actual
  | returnToCaller =>
      cases value : before.register .old with
      | natural n =>
          have registerBits := safe.register .old
          rw [value] at registerBits
          have counterBits : natBits n≤budget := by change 1+natBits n≤budget at registerBits; omega
          have same : {before with pc:=n}=after := Option.some.inj (by
            simpa [controlInstruction,Instruction.execute,value,Cell.nat?] using actual)
          subst after
          exact safe.withPC _ counterBits
      | rational q => simp [controlInstruction,Instruction.execute,value,Cell.nat?] at actual

end PDROC.CalibrationRow.Operand
