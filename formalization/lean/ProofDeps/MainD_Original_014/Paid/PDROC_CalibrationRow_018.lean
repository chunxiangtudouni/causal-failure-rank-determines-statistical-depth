module

public import Paid.PDROC_CalibrationRow_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def boundaryCode : List Instruction :=
  loadSlot 8 .total ++ [.constant .flag (.natural 1),.natOp .subtract .total .total .flag,
    .constant .old (.natural 0),.natCompare .equal .flag .index .old,
    .natCompare .equal .old .index .total,.natOp .add .flag .flag .old]

def boundaryFlag (cursor width : ℕ) : ℕ :=
  (if cursor=0 then 1 else 0)+(if cursor=width-1 then 1 else 0)

def boundaryResult (before : State) (base cursor width : ℕ) : State :=
  let loaded := loadSlotResult before base 8 .total
  let one := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 1)
  let last := ({one with pc:=one.pc+1}).set .total (.natural (width-1))
  let zero := ({last with pc:=last.pc+1}).set .old (.natural 0)
  let left := ({zero with pc:=zero.pc+1}).set .flag (.natural (if cursor=0 then 1 else 0))
  let right := ({left with pc:=left.pc+1}).set .old (.natural (if cursor=width-1 then 1 else 0))
  ({right with pc:=right.pc+1}).set .flag (.natural (boundaryFlag cursor width))

theorem boundary_execute (input : List Cell) (before : State) (base cursor width : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+8 ∈ before.live) (value : before.heap (base+8)=.natural width)
    (index : before.register .index=.natural cursor) :
    linearExecute input boundaryCode before=some (boundaryResult before base cursor width) := by
  simp [boundaryCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Comparison.nat,
    Cell.nat?,fresh,live,value,index,boundaryResult,boundaryFlag,loadSlotResult,Nat.add_assoc]

theorem boundary_fields (before : State) (base cursor width : ℕ) :
    (boundaryResult before base cursor width).heap=before.heap ∧
    (boundaryResult before base cursor width).live=before.live ∧
    (boundaryResult before base cursor width).register .fresh=before.register .fresh ∧
    (boundaryResult before base cursor width).register .index=before.register .index ∧
    (boundaryResult before base cursor width).register .value=before.register .value ∧
    (boundaryResult before base cursor width).register .flag=.natural (boundaryFlag cursor width) ∧
    (boundaryResult before base cursor width).pc=before.pc+9 ∧
    (boundaryResult before base cursor width).output=before.output := by
  simp [boundaryResult,loadSlotResult,State.set,Nat.add_assoc]

theorem boundary_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) :
    LinearFrames region input boundaryCode before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [boundaryCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h|h|h|h|h) <;> subst instruction <;> trivial

theorem boundaryFlag_zero (cursor width : ℕ) :
    boundaryFlag cursor width=0 ↔ cursor≠0 ∧ cursor≠width-1 := by
  simp only [boundaryFlag,Nat.add_eq_zero_iff]
  by_cases h : cursor=0 <;> by_cases k : cursor=width-1 <;> simp [h,k]

theorem boundary_control_execute (input : List Cell) (before : State) (base cursor width origin : ℕ)
    (interior stored : Label) :
    (controlInstruction origin (.branch .flag interior stored)).execute input (boundaryResult before base cursor width)=
      some {boundaryResult before base cursor width with
        pc:=labelAddress origin (if cursor=0 ∨ cursor=width-1 then stored else interior)} := by
  by_cases left : cursor=0 <;> by_cases right : cursor=width-1 <;>
    simp [controlInstruction,Instruction.execute,boundaryResult,State.set,Cell.nat?,boundaryFlag,left,right]

theorem leftRead_decompose : (basicBlock Label.leftRead).body=
    sourceReadCode++channelProductCode 12++boundaryCode := rfl

theorem rightRead_decompose : (basicBlock Label.rightRead).body=
    loadSlot 7 .index++sourceReadCode++channelProductCode 13++boundaryCode := rfl

end PDROC.CalibrationRow
