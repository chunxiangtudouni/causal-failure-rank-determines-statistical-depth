module

public import Paid.PDROC_BitVM_VM_ISA_CodecRefinement_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecRefinement

open Turing PaperProofs.Paid.Computation

/-- The Nat source type is forced by original natToRat success. Its ONE
existing real copy/den1/sign/assemble/cleanup run supplies all semantics;
the new relation merely carries the exact readonly/history/output data. -/
theorem natCast_step (backend : RatBackend) (core : Bool) (target source : Register) :
    StepRefinement backend core ⟨.natToRat target source, rfl⟩ := by
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | rational q => simp [Instruction.execute, sourceValue, Cell.nat?] at success
  | natural value =>
    obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
      _work0, _work24, _work25, _work26, frame, _time, _space⟩ :=
      Codec.NatCast.instruction_runs input target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    have expected : next = Codec.NatCast.logicalAfter logical target value :=
      Option.some.inj (success.symm.trans executed)
    subst next
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have represented := register_observables input logical (Codec.NatCast.logicalAfter logical target value)
      events contents final.stk target ready.toObservables registers rfl rfl rfl frame
    simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

end PDROC.BitVM.VM.ISA.CodecRefinement
