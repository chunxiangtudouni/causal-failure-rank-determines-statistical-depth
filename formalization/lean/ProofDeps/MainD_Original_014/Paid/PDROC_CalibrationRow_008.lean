module

public import Paid.PDROC_CalibrationRow_002
public import Paid.PDROC_CalibrationRow_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def firstPointerCode : List Instruction :=
  [.constant .old (.natural 16),.natOp .add .old .fresh .old]++storeSlot 9 .old

def firstPointerResult (before : State) (base : ℕ) : State :=
  let sixteen := ({before with pc:=before.pc+1}).set .old (.natural 16)
  let computed := ({sixteen with pc:=sixteen.pc+1}).set .old (.natural (base+16))
  storeSlotResult computed base 9 .old

theorem firstPointer_execute (input : List Cell) (before : State) (base : ℕ)
    (fresh : before.register .fresh=.natural base) :
    linearExecute input firstPointerCode before=some (firstPointerResult before base) := by
  simp [firstPointerCode,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,firstPointerResult,storeSlotResult,Nat.add_assoc]

theorem firstPointer_fields (before : State) (base : ℕ) :
    (firstPointerResult before base).heap=Function.update before.heap (base+9) (.natural (firstRow base)) ∧
    (firstPointerResult before base).live=insert (base+9) before.live ∧
    (firstPointerResult before base).register .fresh=before.register .fresh ∧
    (firstPointerResult before base).register .old=.natural (firstRow base) ∧
    (firstPointerResult before base).pc=before.pc+5 ∧
    (firstPointerResult before base).output=before.output := by
  simp [firstPointerResult,storeSlotResult,State.set,firstRow]

def firstPointerPrefixCode : List Instruction :=
  [.constant .old (.natural 16),.natOp .add .old .fresh .old,
    .constant .address (.natural 9),.natOp .add .address .fresh .address]

theorem firstPointer_decompose : firstPointerCode=firstPointerPrefixCode++[.store .address .old] := rfl

theorem firstPointer_prefix_frames (input : List Cell) (before : State) (base M : ℕ)
    (fresh : before.register .fresh=.natural base) : LinearFrames (region base M) input firstPointerCode before := by
  rw [firstPointer_decompose]
  apply single_last_frames (region base M) input firstPointerPrefixCode (.store .address .old)
    before (firstPointerResult before base)
  · intro instruction member state
    simp only [firstPointerPrefixCode,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h <;> subst instruction <;> trivial
  · rw [←firstPointer_decompose]
    exact firstPointer_execute input before base fresh
  · have fields := firstPointer_fields before base
    exact frame_of_one_update (region base M) before _ (base+9) (.natural (firstRow base))
      (header_mem_region base M 9 (by decide) (by decide)) fields.1 fields.2.1

/-- The next eleven original instructions read M from actual header2. -/
def secondPointerCode : List Instruction :=
  loadSlot 2 .index ++
    [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 3),.natOp .add .index .index .flag,
      .natOp .add .total .old .index]++storeSlot 10 .total

def secondPointerResult (before : State) (base M : ℕ) : State :=
  let loaded := loadSlotResult before base 2 .index
  let two := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 2)
  let doubled := ({two with pc:=two.pc+1}).set .index (.natural (M*2))
  let three := ({doubled with pc:=doubled.pc+1}).set .flag (.natural 3)
  let width := ({three with pc:=three.pc+1}).set .index (.natural (M*2+3))
  let computed := ({width with pc:=width.pc+1}).set .total (.natural (firstRow base+(M*2+3)))
  storeSlotResult computed base 10 .total

theorem secondPointer_execute (input : List Cell) (before : State) (base M : ℕ)
    (fresh : before.register .fresh=.natural base) (old : before.register .old=.natural (firstRow base))
    (live : base+2 ∈ before.live) (value : before.heap (base+2)=.natural M) :
    linearExecute input secondPointerCode before=some (secondPointerResult before base M) := by
  simp [secondPointerCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,old,live,value,secondPointerResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem secondPointer_fields (before : State) (base M : ℕ) :
    (secondPointerResult before base M).heap=Function.update before.heap (base+10) (.natural (secondRow base M)) ∧
    (secondPointerResult before base M).live=insert (base+10) before.live ∧
    (secondPointerResult before base M).register .fresh=before.register .fresh ∧
    (secondPointerResult before base M).pc=before.pc+11 ∧
    (secondPointerResult before base M).output=before.output := by
  simp [secondPointerResult,loadSlotResult,storeSlotResult,State.set,secondRow,firstRow,rowWidth,Nat.mul_comm,Nat.add_assoc]

def secondPointerPrefixCode : List Instruction :=
  loadSlot 2 .index ++
    [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 3),.natOp .add .index .index .flag,
      .natOp .add .total .old .index,.constant .address (.natural 10),.natOp .add .address .fresh .address]

theorem secondPointer_decompose : secondPointerCode=secondPointerPrefixCode++[.store .address .total] := rfl

theorem secondPointer_prefix_frames (input : List Cell) (before : State) (base M : ℕ)
    (fresh : before.register .fresh=.natural base) (old : before.register .old=.natural (firstRow base))
    (live : base+2 ∈ before.live) (value : before.heap (base+2)=.natural M) :
    LinearFrames (region base M) input secondPointerCode before := by
  rw [secondPointer_decompose]
  apply single_last_frames (region base M) input secondPointerPrefixCode (.store .address .total)
    before (secondPointerResult before base M)
  · intro instruction member state
    simp only [secondPointerPrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h|h|h)|(h|h|h|h|h|h|h) <;> subst instruction <;> trivial
  · rw [←secondPointer_decompose]
    exact secondPointer_execute input before base M fresh old live value
  · have fields := secondPointer_fields before base M
    exact frame_of_one_update (region base M) before _ (base+10) (.natural (secondRow base M))
      (header_mem_region base M 10 (by decide) (by decide)) fields.1 fields.2.1

theorem buffersCode_decompose : buffersCode=firstPointerCode++secondPointerCode++constantSlot 7 (.natural 0) := rfl

end PDROC.CalibrationRow
