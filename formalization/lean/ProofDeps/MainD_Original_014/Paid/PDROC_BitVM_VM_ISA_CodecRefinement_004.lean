module

public import Paid.PDROC_BitVM_VM_ISA_CodecRefinement_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecRefinement

open Turing PaperProofs.Paid.Computation

/-- Original numeratorAbs: its existing exact actual field/sign run supplies
all new observations. The source Rat type is forced by source success. -/
theorem numeratorAbs_step (backend : RatBackend) (core : Bool) (target source : Register) :
    StepRefinement backend core ⟨.numeratorAbs target source, rfl⟩ := by
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
      _work0, _work24, _work25, _work26, frame, _time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .numeratorAbs target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    have expected : next = Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .numeratorAbs value) :=
      Option.some.inj (success.symm.trans executed)
    subst next
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have represented := register_observables input logical
      (Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .numeratorAbs value))
      events contents final.stk target ready.toObservables registers rfl rfl rfl frame
    simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

/-- Original denominator: its existing exact actual field/sign run supplies
all new observations. The source Rat type is forced by source success. -/
theorem denominator_step (backend : RatBackend) (core : Bool) (target source : Register) :
    StepRefinement backend core ⟨.denominator target source, rfl⟩ := by
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
      _work0, _work24, _work25, _work26, frame, _time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .denominator target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    have expected : next = Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .denominator value) :=
      Option.some.inj (success.symm.trans executed)
    subst next
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have represented := register_observables input logical
      (Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .denominator value))
      events contents final.stk target ready.toObservables registers rfl rfl rfl frame
    simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

/-- Original negative: its existing exact actual field/sign run supplies
all new observations. The source Rat type is forced by source success. -/
theorem negative_step (backend : RatBackend) (core : Bool) (target source : Register) :
    StepRefinement backend core ⟨.negative target source, rfl⟩ := by
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
      _work0, _work24, _work25, _work26, frame, _time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .negative target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    have expected : next = Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .negative value) :=
      Option.some.inj (success.symm.trans executed)
    subst next
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have represented := register_observables input logical
      (Codec.FieldOps.logicalAfter logical target (Codec.FieldOps.Kind.value .negative value))
      events contents final.stk target ready.toObservables registers rfl rfl rfl frame
    simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

/-- Original output uses its existing ONE real Cell-copy/reverse-emit/
TRUE-tick/cleanup run. New output and tick observations are ACTUAL old
macro conclusions; protected bank/history and heap/live are carried. -/
theorem output_step (backend : RatBackend) (core : Bool) (source : Register) :
    StepRefinement backend core ⟨.output source, rfl⟩ := by
  intro input logical next events contents _size ready success
  obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
    _work0, _work24, word, ticks, frame, _time, _space⟩ :=
    Codec.OutputInstruction.instruction_runs input logical source contents Codec.OutputInstruction.clearedStore
      ready.registers ready.outputWord ready.outputTicks
  have expected : next = Codec.OutputInstruction.logicalAfter logical source :=
    Option.some.inj (success.symm.trans executed)
  subst next
  refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
  have represented : Source.Observables input (Codec.OutputInstruction.logicalAfter logical source) events final.stk := by
    refine ⟨registers, ?_, ?_, ready.heap.carry rfl rfl, word, ticks⟩
    · intro field
      exact (frame (Log.BankDrain.bankSlot field)
        (Log.BankDrain.bankSlot_ne field 0 (by decide))
        (Log.BankDrain.bankSlot_ne field 22 (by decide))
        (Log.BankDrain.bankSlot_ne field 24 (by decide))
        (Log.BankDrain.bankSlot_ne field 23 (by decide))).trans (ready.bank field)
    · exact (frame 21 (by decide) (by decide) (by decide) (by decide)).trans ready.history
  simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

end PDROC.BitVM.VM.ISA.CodecRefinement
