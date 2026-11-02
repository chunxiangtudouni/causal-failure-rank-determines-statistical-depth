module

public import Paid.PDROC_BitVM_VM_ISA_Frame_004
public import Paid.PDROC_BitVM_Kernel_Nop_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.MoveRefinement

open Turing PaperProofs.Paid.Computation

/-! Keep old witnesses in their EXACT old Cfg types. At the two public
adapters, static cases on the seven original Register constructors make
moveLabel/moveStore definitionally reduce INSIDE the existential binder
DOMAIN. Ordinary simp of the existential predicate cannot do that.
These finite proof cases neither change code nor duplicate machine runs. -/

private theorem same_semantic (core : Bool) (target : Register) :
    ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
      (events : List Log.HeapEvent) (contents : Stack → List Bool),
      input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
      Instruction.execute input (.move target target) logical = some next →
      ∃ (run : List Kernel.Nop.State) (final : Kernel.Nop.State),
        (run.head? = some (⟨some (), (), contents⟩ : Kernel.Nop.State) ∧
          run.IsChain (fun a b => TM2.step Kernel.Nop.program a = some b) ∧
          run.getLast? = some final ∧ TM2.step Kernel.Nop.program final = none) ∧
        Source.Observables input next (events ++ (Log.eventOf (.move target target) logical).toList) final.stk := by
  intro input logical next events contents _size ready success
  have nextValue : next = Kernel.Nop.after logical :=
    Option.some.inj (success.symm.trans (Kernel.Nop.move_same_execute input logical target))
  subst next
  obtain ⟨run, final, executed, head, chain, last, halt, registers, data, time⟩ :=
    Kernel.Nop.move_same_runs input logical target contents ready.registers
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  simp only [Log.eventOf, Option.toList_none, List.append_nil]
  apply observables_register_from_frame input logical (Kernel.Nop.after logical)
    events contents final.stk ready.toObservables registers rfl rfl rfl
  intro role safe
  exact congrFun data role

private theorem distinct_semantic (core : Bool) (target source : Register) (different : source ≠ target) :
    ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
      (events : List Log.HeapEvent) (contents : Stack → List Bool),
      input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
      Instruction.execute input (.move target source) logical = some next →
      ∃ (run : List Kernel.RegisterGlobal.State) (final : Kernel.RegisterGlobal.State),
        (run.head? = some (⟨some 0, (none, ()), contents⟩ : Kernel.RegisterGlobal.State) ∧
          run.IsChain (fun a b => TM2.step (Kernel.RegisterGlobal.machine source target different) a = some b) ∧
          run.getLast? = some final ∧ TM2.step (Kernel.RegisterGlobal.machine source target different) final = none) ∧
        Source.Observables input next (events ++ (Log.eventOf (.move target source) logical).toList) final.stk := by
  intro input logical next events contents _size ready success
  have specified : Instruction.execute input (.move target source) logical =
      some (({logical with pc := logical.pc + 1}).set target (logical.register source)) := rfl
  have nextValue : next = ({logical with pc := logical.pc + 1}).set target (logical.register source) :=
    Option.some.inj (success.symm.trans specified)
  subst next
  obtain ⟨after, run, final, original, head, chain, last, halt, registers, scratch, time, frame⟩ :=
    Kernel.RegisterGlobal.move_instruction_runs input logical
      (⟨some 0, (none, ()), contents⟩ : Kernel.RegisterGlobal.State) source target different none rfl rfl
      ready.registers (ready.workspace 24 (Or.inr (by decide)))
  have afterSame : after = ({logical with pc := logical.pc + 1}).set target (logical.register source) :=
    Option.some.inj (original.symm.trans specified)
  subst after
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  simp only [Log.eventOf, Option.toList_none, List.append_nil]
  apply observables_register_from_frame input logical _ events contents final.stk
    ready.toObservables registers rfl rfl rfl
  intro role safe
  apply frame
  intro index
  fin_cases index
  · exact protected_not_register role safe source
  · exact protected_not_register role safe target
  · exact protected_not_work role 24 safe (by decide)

private theorem same_resource (core : Bool) (target : Register) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (.move target target) logical = some next →
        ∃ (run : List Kernel.Nop.State) (final : Kernel.Nop.State),
          (run.head? = some (⟨some (), (), contents⟩ : Kernel.Nop.State) ∧
            run.IsChain (fun a b => TM2.step Kernel.Nop.program a = some b) ∧
            run.getLast? = some final ∧ TM2.step Kernel.Nop.program final = none) ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  refine ⟨8, 1, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready _success
  obtain ⟨run, final, executed, head, chain, last, halt, registers, data, time⟩ :=
    Kernel.Nop.move_same_runs input logical target contents ready.registers
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  rw [time, pow_one]
  omega

private theorem distinct_resource (core : Bool) (target source : Register) (different : source ≠ target) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (.move target source) logical = some next →
        ∃ (run : List Kernel.RegisterGlobal.State) (final : Kernel.RegisterGlobal.State),
          (run.head? = some (⟨some 0, (none, ()), contents⟩ : Kernel.RegisterGlobal.State) ∧
            run.IsChain (fun a b => TM2.step (Kernel.RegisterGlobal.machine source target different) a = some b) ∧
            run.getLast? = some final ∧ TM2.step (Kernel.RegisterGlobal.machine source target different) final = none) ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  refine ⟨8, 1, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready _success
  obtain ⟨after, run, final, original, head, chain, last, halt, registers, scratch, time, frame⟩ :=
    Kernel.RegisterGlobal.move_instruction_runs input logical
      (⟨some 0, (none, ()), contents⟩ : Kernel.RegisterGlobal.State) source target different none rfl rfl
      ready.registers (ready.workspace 24 (Or.inr (by decide)))
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  have sourceWord := Kernel.NatInstruction.dataSize_each contents (Kernel.RegisterGlobal.registerSlot source)
  have targetWord := Kernel.NatInstruction.dataSize_each contents (Kernel.RegisterGlobal.registerSlot target)
  rw [ready.registers source] at sourceWord
  rw [ready.registers target] at targetWord
  rw [time, pow_one]
  omega

theorem move_step (backend : RatBackend) (core : Bool) (target source : Register) :
    StepRefinement backend core ⟨.move target source, rfl⟩ := by
  cases source <;> cases target <;> first
    | exact same_semantic core _
    | exact distinct_semantic core _ _ (by decide)

theorem move_resource (backend : RatBackend) (core : Bool) (target source : Register) :
    ResourceRefinement backend core ⟨.move target source, rfl⟩ := by
  cases source <;> cases target <;> first
    | exact same_resource core _
    | exact distinct_resource core _ _ (by decide)

end PDROC.BitVM.VM.ISA.MoveRefinement
