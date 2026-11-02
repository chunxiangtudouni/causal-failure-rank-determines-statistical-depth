module

public import Paid.PDLower_CalibrationCompute_CodeFacts_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def noFresh : Instruction → Bool
  | .constant target _ | .move target _ | .loadInput target _ | .load target _ |
      .natOp _ target _ _ | .ratOp _ target _ _ | .natCompare _ target _ _ | .ratCompare _ target _ _ |
      .natToRat target _ | .numeratorAbs target _ | .denominator target _ | .negative target _ => decide (target ≠ .fresh)
  | _ => true

theorem execute_preserves_fresh (instruction : Instruction) (safe : noFresh instruction = true)
    (input : List Cell) (before after : State) (run : instruction.execute input before = some after) :
    after.register .fresh = before.register .fresh := by
  have stable (register : Register → Cell) (target : Register) (value : Cell) (different : target ≠ .fresh) :
      (Function.update register target value) .fresh = register .fresh := by
    rw [Function.update_apply,ite_eq_right (Ne.symm different)]
  cases instruction <;> simp_all [noFresh,Instruction.execute,State.set,Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument,equation,run⟩ := run)
  all_goals simp_all

theorem linearExecute_preserves_fresh (input : List Cell) (code : List Instruction)
    (safe : ∀ instruction ∈ code,noFresh instruction = true) (before after : State)
    (run : linearExecute input code before = some after) : after.register .fresh = before.register .fresh := by
  induction code generalizing before with
  | nil =>
    have eq : before = after := Option.some.inj run
    subst after
    rfl
  | cons instruction code ih =>
    obtain ⟨middle,step,later⟩ := Option.bind_eq_some_iff.mp run
    exact (ih (fun next member => safe next (by simp only [List.mem_cons]; exact Or.inr member)) middle later).trans
      (execute_preserves_fresh instruction (safe instruction (by simp)) input before middle step)

set_option maxRecDepth 4096 in
theorem basicBlock_noFresh (label : Label) : ∀ instruction ∈ (basicBlock label).body,noFresh instruction = true := by
  have all : (basicBlock label).body.all noFresh = true := by cases label <;> rfl
  exact List.all_eq_true.mp all

theorem kernel_body_preserves_fresh (input : List Cell) (label : Label) (before after : State)
    (run : linearExecute input (basicBlock label).body before = some after) :
    after.register .fresh = before.register .fresh :=
  linearExecute_preserves_fresh input _ (basicBlock_noFresh label) before after run

end PDLower.CalibrationCompute
