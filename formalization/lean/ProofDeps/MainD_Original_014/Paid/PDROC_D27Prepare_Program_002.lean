module

public import Paid.PDROC_D27Prepare_Program_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

def natBinarySlotsResult (before : State) (base left right target value : ℕ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base left .total) base right .value
  let computed := ({loaded with pc:=loaded.pc+1}).set .total (.natural value)
  storeSlotResult computed base target .total

def natToRatSlotResult (before : State) (base source target value : ℕ) : State :=
  let loaded := loadSlotResult before base source .total
  let computed := ({loaded with pc:=loaded.pc+1}).set .total (.rational value)
  storeSlotResult computed base target .total

def comparisonResult (before : State) (base left right : ℕ) (value : Bool) : State :=
  let loaded := loadSlotResult (loadSlotResult before base left .total) base right .value
  ({loaded with pc:=loaded.pc+1}).set .flag (.natural (if value then 1 else 0))

def ceilCoreResult (before : State) (base source target : ℕ) (value : ℚ) : State :=
  let loaded := loadSlotResult before base source .total
  let numerator := ({loaded with pc:=loaded.pc+1}).set .old (.natural value.num.natAbs)
  let denominator := ({numerator with pc:=numerator.pc+1}).set .value (.natural value.den)
  let quotient := ({denominator with pc:=denominator.pc+1}).set .total (.natural (value.num.natAbs/value.den))
  let stored := storeSlotResult quotient base target .total
  ({stored with pc:=stored.pc+1}).set .flag (.natural (value.num.natAbs%value.den))

theorem natBinarySlots_execute (input : List Cell) (before : State)
    (base left right target : ℕ) (operation : NatOp) (x y value : ℕ)
    (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.natural x) (hright : before.heap (base+right)=.natural y)
    (hoperation : operation.eval x y=some value) :
    linearExecute input (natBinarySlots operation left right target) before=
      some (natBinarySlotsResult before base left right target value) := by
  simp only [NatOp.eval] at hoperation
  simp [natBinarySlots,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,hbase,hleftLive,hrightLive,hleft,hright,hoperation,
    natBinarySlotsResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem natBinarySlotsResult_fields (before : State) (base left right target value : ℕ) :
    (natBinarySlotsResult before base left right target value).heap=
      Function.update before.heap (base+target) (.natural value) ∧
    (natBinarySlotsResult before base left right target value).live=insert (base+target) before.live ∧
    (natBinarySlotsResult before base left right target value).register .fresh=before.register .fresh ∧
    (natBinarySlotsResult before base left right target value).pc=before.pc+10 ∧
    (natBinarySlotsResult before base left right target value).output=before.output := by
  simp [natBinarySlotsResult,loadSlotResult,storeSlotResult,State.set]

theorem natToRatSlot_execute (input : List Cell) (before : State) (base source target value : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+source ∈ before.live)
    (hvalue : before.heap (base+source)=.natural value) :
    linearExecute input (natToRatSlot source target) before=
      some (natToRatSlotResult before base source target value) := by
  simp [natToRatSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,hbase,hlive,hvalue,natToRatSlotResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem natToRatSlotResult_fields (before : State) (base source target value : ℕ) :
    (natToRatSlotResult before base source target value).heap=
      Function.update before.heap (base+target) (.rational value) ∧
    (natToRatSlotResult before base source target value).live=insert (base+target) before.live ∧
    (natToRatSlotResult before base source target value).register .fresh=before.register .fresh ∧
    (natToRatSlotResult before base source target value).pc=before.pc+7 ∧
    (natToRatSlotResult before base source target value).output=before.output := by
  simp [natToRatSlotResult,loadSlotResult,storeSlotResult,State.set]

theorem natCompareSlots_execute (input : List Cell) (before : State) (base left right x y : ℕ)
    (comparison : Comparison) (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.natural x) (hright : before.heap (base+right)=.natural y) :
    linearExecute input (natCompareSlots comparison left right) before=
      some (comparisonResult before base left right (comparison.nat x y)) := by
  simp [natCompareSlots,loadSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,hbase,hleftLive,hrightLive,hleft,hright,
    comparisonResult,loadSlotResult,Nat.add_assoc]

theorem ratCompareSlots_execute (input : List Cell) (before : State) (base left right : ℕ)
    (x y : ℚ) (comparison : Comparison) (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.rational x) (hright : before.heap (base+right)=.rational y) :
    linearExecute input (ratCompareSlots comparison left right) before=
      some (comparisonResult before base left right (comparison.rat x y)) := by
  simp [ratCompareSlots,loadSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,Cell.rat?,hbase,hleftLive,hrightLive,hleft,hright,
    comparisonResult,loadSlotResult,Nat.add_assoc]

theorem comparisonResult_fields (before : State) (base left right : ℕ) (value : Bool) :
    (comparisonResult before base left right value).heap=before.heap ∧
    (comparisonResult before base left right value).live=before.live ∧
    (comparisonResult before base left right value).register .fresh=before.register .fresh ∧
    (comparisonResult before base left right value).register .flag=.natural (if value then 1 else 0) ∧
    (comparisonResult before base left right value).pc=before.pc+7 ∧
    (comparisonResult before base left right value).output=before.output := by
  simp [comparisonResult,loadSlotResult,State.set]

theorem ceilCore_execute (input : List Cell) (before : State) (base source target : ℕ) (value : ℚ)
    (hbase : before.register .fresh=.natural base) (hlive : base+source ∈ before.live)
    (hvalue : before.heap (base+source)=.rational value) :
    linearExecute input (ceilCore source target) before=some (ceilCoreResult before base source target value) := by
  have hnz : value.den ≠ 0 := Nat.ne_of_gt value.den_pos
  simp [ceilCore,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,Cell.rat?,hbase,hlive,hvalue,hnz,
    ceilCoreResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem ceilCoreResult_fields (before : State) (base source target : ℕ) (value : ℚ) :
    (ceilCoreResult before base source target value).heap=
      Function.update before.heap (base+target) (.natural (value.num.natAbs/value.den)) ∧
    (ceilCoreResult before base source target value).live=insert (base+target) before.live ∧
    (ceilCoreResult before base source target value).register .fresh=before.register .fresh ∧
    (ceilCoreResult before base source target value).register .flag=.natural (value.num.natAbs%value.den) ∧
    (ceilCoreResult before base source target value).pc=before.pc+10 ∧
    (ceilCoreResult before base source target value).output=before.output := by
  simp [ceilCoreResult,loadSlotResult,storeSlotResult,State.set]

theorem natBinarySlots_straight (operation : NatOp) (left right target : ℕ) :
    StraightCode (natBinarySlots operation left right target) := by
  intro instruction member
  simp only [natBinarySlots,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (((h|h|h)|(h|h|h))|h)|(h|h|h) <;> subst instruction <;> trivial

theorem natToRatSlot_straight (source target : ℕ) : StraightCode (natToRatSlot source target) := by
  intro instruction member
  simp only [natToRatSlot,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|h)|(h|h|h) <;> subst instruction <;> trivial

theorem natCompareSlots_straight (comparison : Comparison) (left right : ℕ) :
    StraightCode (natCompareSlots comparison left right) := by
  intro instruction member
  simp only [natCompareSlots,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|h <;> subst instruction <;> trivial

theorem ratCompareSlots_straight (comparison : Comparison) (left right : ℕ) :
    StraightCode (ratCompareSlots comparison left right) := by
  intro instruction member
  simp only [ratCompareSlots,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|h <;> subst instruction <;> trivial

theorem ceilCore_straight (source target : ℕ) : StraightCode (ceilCore source target) := by
  intro instruction member
  simp only [ceilCore,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (((h|h|h)|(h|h|h))|(h|h|h))|h <;> subst instruction <;> trivial

theorem fetches_page_part (page : ℕ) (hpage : page < pageCount) (prelude code suffix : List Instruction)
    (heq : pageCode page=prelude++code++suffix) : FetchesCode program (pc page+prelude.length) code := by
  intro offset hoffset
  have hb : prelude.length+offset < (pageCode page).length := by rw [heq]; simp only [List.length_append]; omega
  have hf := fetches_page page hpage (prelude.length+offset) hb
  rw [heq,List.append_assoc,List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left,List.getElem?_append_left hoffset] at hf
  simpa only [Nat.add_assoc] using hf

theorem jump_step (input : List Cell) (before : State) (target : ℕ)
    (fetch : program[before.pc]?=some (.jump target)) :
    step program input before=some {before with pc:=target} := by
  simp [step,fetch,Instruction.execute]

theorem branch_step (input : List Cell) (before : State) (whenZero whenNonzero value : ℕ)
    (fetch : program[before.pc]?=some (.branchZero .flag whenZero whenNonzero))
    (flag : before.register .flag=.natural value) :
    step program input before=some {before with pc:=if value=0 then whenZero else whenNonzero} := by
  simp [step,fetch,Instruction.execute,flag,Cell.nat?]

end PDROC.D27Prepare.Program
