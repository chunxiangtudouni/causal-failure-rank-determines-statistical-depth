module

public import Paid.PDROC_BitVM_VM_ISA_Frame_004
public import Paid.PDROC_BitVM_Kernel_RatCompareInstruction_058

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

theorem rat_operands (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (operation : RatOp) (target left right : Register)
    (success : Instruction.execute input (.ratOp operation target left right) logical = some next) :
    ∃ x y result : Rat, logical.register left = .rational x ∧ logical.register right = .rational y ∧
      operation.eval x y = some result ∧ next = Kernel.RawInstruction.after logical target result := by
  cases leftValue : logical.register left with
  | natural a => simp [Instruction.execute,leftValue,Cell.rat?] at success
  | rational x =>
    cases rightValue : logical.register right with
    | natural b => simp [Instruction.execute,leftValue,rightValue,Cell.rat?] at success
    | rational y =>
      cases evaluated : operation.eval x y with
      | none => simp [Instruction.execute,leftValue,rightValue,Cell.rat?,evaluated] at success
      | some result =>
        have original := Kernel.RawInstruction.original_execute input logical operation target left right x y result
          leftValue rightValue evaluated
        exact ⟨x,y,result,rfl,rfl,evaluated,Option.some.inj (success.symm.trans original)⟩

theorem compare_operands (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (comparison : Comparison) (target left right : Register)
    (success : Instruction.execute input (.ratCompare comparison target left right) logical = some next) :
    ∃ x y : Rat, logical.register left = .rational x ∧ logical.register right = .rational y ∧
      next = Kernel.RatCompare.after logical comparison target x y := by
  cases leftValue : logical.register left with
  | natural a => simp [Instruction.execute,leftValue,Cell.rat?] at success
  | rational x =>
    cases rightValue : logical.register right with
    | natural b => simp [Instruction.execute,leftValue,rightValue,Cell.rat?] at success
    | rational y =>
      have original := Kernel.RatCompare.original_execute input logical comparison target left right x y leftValue rightValue
      exact ⟨x,y,rfl,rfl,Option.some.inj (success.symm.trans original)⟩

theorem rat_step (backend : RatBackend) (core : Bool) (operation : RatOp) (target left right : Register) :
    StepRefinement backend core ⟨.ratOp operation target left right,rfl⟩ := by
  intro input logical next events contents _size ready success
  obtain ⟨x,y,result,leftRat,rightRat,evaluated,same⟩ := rat_operands input logical next operation target left right success
  subst next
  obtain ⟨run,final,_original,head,chain,last,halt,registers,_work0,_work24,_work25,_work29,_time,frame⟩ :=
    Kernel.RawInstruction.instruction_runs (backend.machine operation) operation
      (Kernel.RawInstruction.resultFunction operation) (backend.c operation) (backend.d operation)
      (backend.valid operation).2.2.1 (backend.valid operation).2.2.2 input logical target left right
      x y result contents ready.registers leftRat rightRat evaluated
      (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
  refine ⟨run,final,⟨head,chain,last,halt⟩,?_⟩
  have observed : Source.Observables input (Kernel.RawInstruction.after logical target result) events final.stk := by
    apply observables_register_from_frame input logical _ events contents final.stk ready.toObservables registers rfl rfl rfl
    intro role safe
    exact frame role (protected_not_zero role safe) (protected_not_work role 24 safe (by decide))
      (protected_not_work role 25 safe (by decide)) (protected_not_work role 29 safe (by decide))
      (protected_not_register role safe target)
  simpa [Log.eventOf] using observed

theorem rat_compare_step (backend : RatBackend) (core : Bool) (comparison : Comparison) (target left right : Register) :
    StepRefinement backend core ⟨.ratCompare comparison target left right,rfl⟩ := by
  intro input logical next events contents _size ready success
  obtain ⟨x,y,leftRat,rightRat,same⟩ := compare_operands input logical next comparison target left right success
  subst next
  obtain ⟨run,final,_original,head,chain,last,halt,registers,_work0,_work24,_work25,_work29,_time,frame⟩ :=
    Kernel.RatCompare.instruction_runs (backend.machine .subtract) comparison (backend.c .subtract) (backend.d .subtract)
      (backend.valid .subtract).2.2.1 input logical target left right x y contents ready.registers leftRat rightRat
      (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
  refine ⟨run,final,⟨head,chain,last,halt⟩,?_⟩
  have observed : Source.Observables input (Kernel.RatCompare.after logical comparison target x y) events final.stk := by
    apply observables_register_from_frame input logical _ events contents final.stk ready.toObservables registers rfl rfl rfl
    intro role safe
    exact frame role (protected_not_zero role safe) (protected_not_work role 24 safe (by decide))
      (protected_not_work role 25 safe (by decide)) (protected_not_work role 29 safe (by decide))
      (protected_not_register role safe target)
  simpa [Log.eventOf] using observed

end PDROC.BitVM.VM.ISA
