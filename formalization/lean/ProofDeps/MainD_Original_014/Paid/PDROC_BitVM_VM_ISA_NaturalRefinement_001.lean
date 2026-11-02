module

public import Paid.PDROC_BitVM_VM_ISA_Frame_004
public import Paid.PDROC_BitVM_Kernel_NatInstruction_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.NaturalRefinement

open Turing PaperProofs.Paid.Computation

/-! The source successful step supplies both Nat operands and evalSome.
In particular native divide/modulo-zero conventions cannot create an
original successful step. These are source-only integration drafts. -/

theorem successful_operands (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register)
    (success : Instruction.execute input (.natOp operation target left right) logical = some next) :
    ∃ a b result : ℕ, logical.register left = .natural a ∧ logical.register right = .natural b ∧
      operation.eval a b = some result ∧ next = Kernel.NatInstruction.after logical target result := by
  cases leftValue : logical.register left with
  | rational value => simp [Instruction.execute, leftValue, Cell.nat?] at success
  | natural a =>
    cases rightValue : logical.register right with
    | rational value => simp [Instruction.execute, leftValue, rightValue, Cell.nat?] at success
    | natural b =>
      cases evaluated : operation.eval a b with
      | none => simp [Instruction.execute, leftValue, rightValue, Cell.nat?, evaluated] at success
      | some result =>
        refine ⟨a, b, result, rfl, rfl, evaluated, ?_⟩
        exact Option.some.inj (success.symm.trans
          (Kernel.NatInstruction.execute input logical operation target left right a b result leftValue rightValue evaluated))

theorem natural_step (backend : RatBackend) (core : Bool)
    (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) :
    StepRefinement backend core ⟨.natOp operation target left right, rfl⟩ := by
  intro input logical next events contents size ready success
  obtain ⟨a, b, result, leftNat, rightNat, evaluated, nextValue⟩ :=
    successful_operands input logical next operation target left right success
  subst next
  obtain ⟨run, final, executed, head, chain, last, halt, registers, work0, work24, time, frame⟩ :=
    Kernel.NatInstruction.instruction_runs input logical operation target left right a b result contents none
      ready.registers leftNat rightNat evaluated
      (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
  have protectedFrame : ∀ role, Protected role → final.stk role = contents role := by
    intro role safe
    exact frame role (protected_not_zero role safe) (protected_not_work role 24 safe (by decide))
      (protected_not_register role safe target)
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  simp only [Log.eventOf, Option.toList_none, List.append_nil]
  exact observables_register_from_frame input logical (Kernel.NatInstruction.after logical target result)
    events contents final.stk ready.toObservables registers rfl rfl rfl protectedFrame

end PDROC.BitVM.VM.ISA.NaturalRefinement
