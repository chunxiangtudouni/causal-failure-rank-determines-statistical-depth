module

public import Paid.PDCompute_SolverSequenceMemory_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute storeSlot)
open PDMenu.ComputeFrame

/-- One real dense-record cell read. The source pointer uses old while
the saved caller return remains in live header1. Store-address scratch
therefore cannot destroy the streaming source pointer. -/
def denseReadCellCode (target : ℕ) : List Instruction :=
  [.load .total .old]++storeSlot target .total++
    [.constant .flag (.natural 1),.natOp .add .old .old .flag]

def denseReadCellResult (before : State) (base target pointer : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update
      (Function.update before.register .total (before.heap pointer)) .address (.natural (base+target)))
      .flag (.natural 1)) .old (.natural (pointer+1))
    heap:=Function.update before.heap (base+target) (before.heap pointer)
    live:=insert (base+target) before.live
    pc:=before.pc+6}

theorem denseReadCellCode_length (target : ℕ) : (denseReadCellCode target).length=6 := rfl

theorem denseReadCellCode_straight (target : ℕ) : StraightCode (denseReadCellCode target) := by
  intro instruction member
  simp only [denseReadCellCode,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|(h|h|h))|(h|h) <;> subst instruction <;> trivial

theorem denseReadCellCode_execute (input : List Cell) (before : State) (base target pointer : ℕ)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (hlive : pointer ∈ before.live) :
    linearExecute input (denseReadCellCode target) before=some (denseReadCellResult before base target pointer) := by
  simp [denseReadCellCode,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,hpointer,hlive,denseReadCellResult,Nat.add_assoc]

theorem denseReadCellResult_fields (before : State) (base target pointer : ℕ) :
    (denseReadCellResult before base target pointer).heap=Function.update before.heap (base+target) (before.heap pointer) ∧
    (denseReadCellResult before base target pointer).live=insert (base+target) before.live ∧
    (denseReadCellResult before base target pointer).register .fresh=before.register .fresh ∧
    (denseReadCellResult before base target pointer).register .old=.natural (pointer+1) ∧
    (denseReadCellResult before base target pointer).pc=before.pc+6 ∧
    (denseReadCellResult before base target pointer).output=before.output := by
  simp [denseReadCellResult]

theorem Header.denseReadCell {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (target pointer : ℕ) :
    Header (denseReadCellResult before base target pointer) base (Function.update values target (before.heap pointer)) := by
  apply Header.update header target (before.heap pointer) (denseReadCellResult_fields ..).1
  rw [(denseReadCellResult_fields before base target pointer).2.1]
  exact Finset.subset_insert _ _

theorem denseReadCellCode_prefix_memory (input : List Cell) (before after : State) (base target pointer : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : target < headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (hlive : pointer ∈ before.live) (count : ℕ) (hcount : count ≤ 6)
    (hexec : linearExecute input ((denseReadCellCode target).take count) before=some after) :
    HeaderMemory before after base := by
  interval_cases count <;>
    simp [denseReadCellCode,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,hpointer,hlive] at hexec <;> subst after
  all_goals first
    | exact HeaderMemory.of_unchanged base rfl rfl rfl
    | exact HeaderMemory.write header target inside (before.heap pointer) rfl rfl rfl

end PDCompute.Solver
