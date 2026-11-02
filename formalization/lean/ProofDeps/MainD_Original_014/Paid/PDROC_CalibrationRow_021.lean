module

public import Paid.PDROC_CalibrationRow_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def interiorCode (right : Bool) : List Instruction :=
  [.constant .flag (.natural 1),
    if right then .natOp .add .index .index .flag else .natOp .subtract .index .index .flag]

def interiorResult (before : State) (right : Bool) (cursor : ℕ) : State :=
  let one := ({before with pc:=before.pc+1}).set .flag (.natural 1)
  ({one with pc:=one.pc+1}).set .index (.natural (if right then cursor+1 else cursor-1))

theorem interior_execute (input : List Cell) (before : State) (right : Bool) (cursor : ℕ)
    (index : before.register .index=.natural cursor) :
    linearExecute input (interiorCode right) before=some (interiorResult before right cursor) := by
  cases right <;> simp [interiorCode,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,index,interiorResult,Nat.add_assoc]

theorem interior_fields (before : State) (right : Bool) (cursor : ℕ) :
    (interiorResult before right cursor).heap=before.heap ∧
    (interiorResult before right cursor).live=before.live ∧
    (interiorResult before right cursor).register .fresh=before.register .fresh ∧
    (interiorResult before right cursor).register .index=.natural (if right then cursor+1 else cursor-1) ∧
    (interiorResult before right cursor).register .value=before.register .value ∧
    (interiorResult before right cursor).pc=before.pc+2 ∧
    (interiorResult before right cursor).output=before.output := by
  simp [interiorResult,State.set,Nat.add_assoc]

theorem interior_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) (right : Bool) :
    LinearFrames region input (interiorCode right) before := by
  cases right <;> apply LinearFrames.of_static <;>
    intro instruction member state <;>
    simp only [interiorCode,Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member <;>
    rcases member with h|h <;> subst instruction <;> trivial

theorem leftInterior_body : (basicBlock Label.leftInterior).body=interiorCode false := rfl
theorem rightInterior_body : (basicBlock Label.rightInterior).body=interiorCode true := rfl

def letterTarget (level cursor : ℕ) (right : Bool) : ℕ :=
  if cursor=0 ∨ cursor=2*level then cursor else if right then cursor+1 else cursor-1

theorem letterTarget_left (level cursor : ℕ) (inside : cursor<2*level+1) :
    (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val=letterTarget level cursor false := by
  by_cases boundary : cursor=0 ∨ cursor=2*level <;> simp [walkMove,letterTarget,boundary]

theorem letterTarget_right (level cursor : ℕ) (inside : cursor<2*level+1) :
    (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val=letterTarget level cursor true := by
  by_cases boundary : cursor=0 ∨ cursor=2*level <;> simp [walkMove,letterTarget,boundary]

end PDROC.CalibrationRow
