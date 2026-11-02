module

public import Paid.PDROC_BitVM_VM_ISA_AllData_001
public import Paid.PDROC_BitVM_VM_Source_LocalPolynomial_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.AllData

open Turing PaperProofs.Paid.Computation

/-- Uniform constants for any FIXED FINITE source-position catalogue,
chosen BEFORE all original inputs and caller data. There is deliberately
no Fintype Instruction/DataInstruction assumption: literals remain fixed
source syntax, while the actual compiler supplies finite positions. -/
theorem finite_complete {I : Type*} [Fintype I] (backend : RatBackend) (core : Bool)
    (data : I → DataInstruction) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
      ∀ (index : I) (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input (data index).val logical = some next →
        ∃ (run : List (State backend (data index))) (final : State backend (data index)),
          ActualRun backend core (data index) contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf (data index).val logical).toList) final.stk ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  classical
  choose coefficient degree _positiveCoefficient _positiveDegree chosen using
    (fun index : I => complete backend core (data index))
  obtain ⟨C, D, positiveC, positiveD, uniform⟩ := Source.finite_local_polynomial coefficient degree
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro index input logical next events contents size ready success
  obtain ⟨run, final, actual, observed, time⟩ := chosen index input logical next events contents size ready success
  refine ⟨run, final, actual, observed, time.trans ?_⟩
  exact uniform index (Kernel.NatInstruction.dataSize contents + (encodeBits input).length)

end PDROC.BitVM.VM.ISA.AllData
