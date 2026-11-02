module

public import Paid.PDROC_CalibrationRow_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- This is the original five-instruction physical read-row fetch.
The row cell is fetched through actual header9; no row-value oracle is
part of the program. The theorem connects it to the caller's RowAt. -/
def sourceReadCode : List Instruction :=
  loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address]

def sourceReadResult (before : State) (base rowBase cursor : ℕ) (mass : ℚ) : State :=
  let pointer := loadSlotResult before base 9 .old
  let addressed := ({pointer with pc:=pointer.pc+1}).set .address (.natural (rowBase+cursor))
  ({addressed with pc:=addressed.pc+1}).set .value (.rational mass)

theorem sourceRead_execute (input : List Cell) (before : State) (base rowBase cursor : ℕ) (mass : ℚ)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+9 ∈ before.live) (pointer : before.heap (base+9)=.natural rowBase)
    (index : before.register .index=.natural cursor)
    (cellLive : rowBase+cursor ∈ before.live) (cell : before.heap (rowBase+cursor)=.rational mass) :
    linearExecute input sourceReadCode before=some (sourceReadResult before base rowBase cursor mass) := by
  simp [sourceReadCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,pointerLive,pointer,index,cellLive,cell,sourceReadResult,loadSlotResult,Nat.add_assoc]

theorem sourceRead_fields (before : State) (base rowBase cursor : ℕ) (mass : ℚ) :
    (sourceReadResult before base rowBase cursor mass).heap=before.heap ∧
    (sourceReadResult before base rowBase cursor mass).live=before.live ∧
    (sourceReadResult before base rowBase cursor mass).register .fresh=before.register .fresh ∧
    (sourceReadResult before base rowBase cursor mass).register .index=before.register .index ∧
    (sourceReadResult before base rowBase cursor mass).register .value=.rational mass ∧
    (sourceReadResult before base rowBase cursor mass).pc=before.pc+5 ∧
    (sourceReadResult before base rowBase cursor mass).output=before.output := by
  simp [sourceReadResult,loadSlotResult,State.set,Nat.add_assoc]

def channelProductCode (biasOffset : ℕ) : List Instruction :=
  loadSlot biasOffset .old ++ [.ratOp .multiply .value .value .old]

def channelProductResult (before : State) (base biasOffset : ℕ) (mass probability : ℚ) : State :=
  let loaded := loadSlotResult before base biasOffset .old
  ({loaded with pc:=loaded.pc+1}).set .value (.rational (mass*probability))

theorem channelProduct_execute (input : List Cell) (before : State) (base biasOffset : ℕ) (mass probability : ℚ)
    (fresh : before.register .fresh=.natural base)
    (biasLive : base+biasOffset ∈ before.live) (bias : before.heap (base+biasOffset)=.rational probability)
    (value : before.register .value=.rational mass) :
    linearExecute input (channelProductCode biasOffset) before=
      some (channelProductResult before base biasOffset mass probability) := by
  simp [channelProductCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,RatOp.eval,
    Cell.nat?,Cell.rat?,fresh,biasLive,bias,value,channelProductResult,loadSlotResult,Nat.add_assoc]

theorem channelProduct_fields (before : State) (base biasOffset : ℕ) (mass probability : ℚ) :
    (channelProductResult before base biasOffset mass probability).heap=before.heap ∧
    (channelProductResult before base biasOffset mass probability).live=before.live ∧
    (channelProductResult before base biasOffset mass probability).register .fresh=before.register .fresh ∧
    (channelProductResult before base biasOffset mass probability).register .index=before.register .index ∧
    (channelProductResult before base biasOffset mass probability).register .value=.rational (mass*probability) ∧
    (channelProductResult before base biasOffset mass probability).pc=before.pc+4 ∧
    (channelProductResult before base biasOffset mass probability).output=before.output := by
  simp [channelProductResult,loadSlotResult,State.set,Nat.add_assoc]

theorem sourceRead_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) :
    LinearFrames region input sourceReadCode before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [sourceReadCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h) <;> subst instruction <;> trivial

theorem channelProduct_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) (biasOffset : ℕ) :
    LinearFrames region input (channelProductCode biasOffset) before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [channelProductCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|h <;> subst instruction <;> trivial

end PDROC.CalibrationRow
