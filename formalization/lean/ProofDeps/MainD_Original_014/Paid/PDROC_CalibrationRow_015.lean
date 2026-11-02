module

public import Paid.PDROC_CalibrationRow_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem Buffers.read_mem (base M read write index : ℕ) (buffers : Buffers base M read write)
    (inside : index < rowWidth M) : read+index ∈ region base M := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact first_mem_region base M index inside
  · exact second_mem_region base M index inside

theorem Buffers.write_mem (base M read write index : ℕ) (buffers : Buffers base M read write)
    (inside : index < rowWidth M) : write+index ∈ region base M := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact second_mem_region base M index inside
  · exact first_mem_region base M index inside

theorem Buffers.write_header_ne (base M read write index offset : ℕ) (buffers : Buffers base M read write)
    (headerOffset : offset < 16) : write+index ≠ base+offset := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> omega

/-- Exact six-instruction prefix of original zeroCell, before the
eight-instruction cursor increment. It writes actual rational zero. -/
def zeroWriteCode : List Instruction :=
  loadSlot 10 .old ++ [.natOp .add .address .old .index,.constant .value (.rational 0),.store .address .value]

def zeroWriteResult (before : State) (base rowBase cursor : ℕ) : State :=
  let loaded := loadSlotResult before base 10 .old
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural (rowBase+cursor))
  let zeroed := ({addressed with pc:=addressed.pc+1}).set .value (.rational 0)
  writeCell zeroed (rowBase+cursor) (.rational 0)

theorem zeroWrite_execute (input : List Cell) (before : State) (base rowBase cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointerValue : before.heap (base+10)=.natural rowBase)
    (index : before.register .index=.natural cursor) :
    linearExecute input zeroWriteCode before=some (zeroWriteResult before base rowBase cursor) := by
  simp [zeroWriteCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,pointerLive,pointerValue,index,zeroWriteResult,loadSlotResult,writeCell,Nat.add_assoc]

theorem zeroWrite_fields (before : State) (base rowBase cursor : ℕ) :
    (zeroWriteResult before base rowBase cursor).heap=
      Function.update before.heap (rowBase+cursor) (.rational 0) ∧
    (zeroWriteResult before base rowBase cursor).live=insert (rowBase+cursor) before.live ∧
    (zeroWriteResult before base rowBase cursor).register .fresh=before.register .fresh ∧
    (zeroWriteResult before base rowBase cursor).register .index=before.register .index ∧
    (zeroWriteResult before base rowBase cursor).pc=before.pc+6 ∧
    (zeroWriteResult before base rowBase cursor).output=before.output := by
  simp [zeroWriteResult,loadSlotResult,writeCell,State.set,Nat.add_assoc]

def zeroWritePrefixCode : List Instruction :=
  loadSlot 10 .old ++ [.natOp .add .address .old .index,.constant .value (.rational 0)]

theorem zeroWrite_decompose : zeroWriteCode=zeroWritePrefixCode++[.store .address .value] := rfl

theorem zeroCell_decompose : (basicBlock Label.zeroCell).body=zeroWriteCode++incrementSlot 7 := rfl

theorem zeroWrite_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (base rowBase cursor : ℕ) (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointerValue : before.heap (base+10)=.natural rowBase)
    (index : before.register .index=.natural cursor) (inside : rowBase+cursor ∈ region) :
    LinearFrames region input zeroWriteCode before := by
  rw [zeroWrite_decompose]
  apply single_last_frames region input zeroWritePrefixCode (.store .address .value)
    before (zeroWriteResult before base rowBase cursor)
  · intro instruction member state
    simp only [zeroWritePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h|h|h)|(h|h) <;> subst instruction <;> trivial
  · rw [←zeroWrite_decompose]
    exact zeroWrite_execute input before base rowBase cursor fresh pointerLive pointerValue index
  · have fields := zeroWrite_fields before base rowBase cursor
    exact frame_of_one_update region before _ (rowBase+cursor) (.rational 0) inside fields.1 fields.2.1

end PDROC.CalibrationRow
