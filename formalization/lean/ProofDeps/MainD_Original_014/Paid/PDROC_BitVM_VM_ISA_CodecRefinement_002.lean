module

public import Paid.PDROC_BitVM_VM_ISA_CodecRefinement_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecRefinement

open Turing PaperProofs.Paid.Computation

/-- Exactly the already-passed original three-way natural comparison
path, viewed through the fixed data-directory entry. Both actual typed
operands follow from the original successful step, not extra input. -/
theorem natCompare_step (backend : RatBackend) (core : Bool) (comparison : Comparison)
    (target left right : Register) :
    StepRefinement backend core ⟨.natCompare comparison target left right, rfl⟩ := by
  intro input logical next events contents _size ready success
  cases leftValue : logical.register left with
  | rational q => simp [Instruction.execute, leftValue, Cell.nat?] at success
  | natural a =>
    cases rightValue : logical.register right with
    | rational q => simp [Instruction.execute, leftValue, rightValue, Cell.nat?] at success
    | natural b =>
      obtain ⟨run, final, executed, head, chain, last, halt, _store, registers,
        _work0, _work24, _work25, _work26, frame, _time, _space⟩ :=
        Codec.NatCompare.instruction_runs input comparison target left right logical a b contents
          Codec.NatCompare.clearedStore ready.registers leftValue rightValue
      have expected : next = Codec.NatCompare.logicalAfter comparison logical target a b :=
        Option.some.inj (success.symm.trans executed)
      subst next
      refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
      have represented := register_observables input logical
        (Codec.NatCompare.logicalAfter comparison logical target a b) events contents final.stk target
        ready.toObservables registers rfl rfl rfl frame
      simpa only [Log.eventOf, Option.toList_none, List.append_nil] using represented

end PDROC.BitVM.VM.ISA.CodecRefinement
