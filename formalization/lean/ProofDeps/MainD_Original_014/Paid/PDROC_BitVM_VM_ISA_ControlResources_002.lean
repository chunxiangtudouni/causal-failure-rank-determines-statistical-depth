module

public import Paid.PDROC_BitVM_VM_ISA_ControlResources_001
public import Paid.PDROC_BitVM_VM_Source_LocalPolynomial_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.ControlResources

open Turing PaperProofs.Paid.Computation

/-! SOURCE ONLY. The finite index is the FIXED source-position table,
not the infinite Instruction syntax and never an input word width. -/

theorem finite_complete {I : Type*} [Fintype I] (code : Program)
    (instructions : I → ControlInstruction) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (index : I) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        Source.Ready input logical events contents →
        Instruction.execute input (instructions index).val logical = some next →
        ∃ (run : List (ControlCatalog.State code (instructions index)))
          (final : ControlCatalog.State code (instructions index)),
          ControlCatalog.ActualRun code (instructions index) contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf (instructions index).val logical).toList) final.stk ∧
          ControlCatalog.NextMatches code (ControlCatalog.observedNext code (instructions index) final.var) next.pc ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  classical
  choose coefficient degree _positiveCoefficient _positiveDegree chosen using
    (fun index : I => complete code (instructions index))
  obtain ⟨C, D, positiveC, positiveD, uniform⟩ := Source.finite_local_polynomial coefficient degree
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro index input logical next events contents ready success
  obtain ⟨run, final, actual, observed, selected, time⟩ :=
    chosen index input logical next events contents ready success
  refine ⟨run, final, actual, observed, selected, time.trans ?_⟩
  exact uniform index (Kernel.NatInstruction.dataSize contents + (encodeBits input).length)

end PDROC.BitVM.VM.ISA.ControlResources
