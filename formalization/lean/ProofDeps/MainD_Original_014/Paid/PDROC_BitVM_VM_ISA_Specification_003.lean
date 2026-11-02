module

public import Paid.PDROC_BitVM_VM_ISA_Macros_002
public import Paid.PDROC_BitVM_VM_Source_Representation_006
public import Paid.PDROC_BitVM_Kernel_Trace_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

def ActualRun (backend : RatBackend) (core : Bool) (data : DataInstruction)
    (contents : Stack → List Bool) (run : List (State backend data)) (final : State backend data) : Prop :=
  run.head? = some (before backend data contents) ∧
  run.IsChain (fun a b => TM2.step (program backend core data) a = some b) ∧
  run.getLast? = some final ∧ TM2.step (program backend core data) final = none

/-- Internal compiler obligation, discharged by the actual opcode
implementations. The history is the exact appended original event,
not merely some replay-equivalent unbounded list of heap records. -/
def StepRefinement (backend : RatBackend) (core : Bool) (data : DataInstruction) : Prop :=
  ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool),
    input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
    Instruction.execute input data.val logical = some next →
    ∃ (run : List (State backend data)) (final : State backend data),
      ActualRun backend core data contents run final ∧
      Source.Observables input next (events ++ (Log.eventOf data.val logical).toList) final.stk

/-- All resource constants precede all inputs. Resource and semantic
proofs may reuse different old theorems: deterministic full-run
uniqueness below identifies their entire selected paths, not just their
answers. This is an internal property of fixed actual opcode code. -/
def ResourceRefinement (backend : RatBackend) (core : Bool) (data : DataInstruction) : Prop :=
  ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
    ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
      (events : List Log.HeapEvent) (contents : Stack → List Bool),
      input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
      Instruction.execute input data.val logical = some next →
      ∃ (run : List (State backend data)) (final : State backend data),
        ActualRun backend core data contents run final ∧
        run.length ≤ C*(Kernel.NatInstruction.dataSize contents+(encodeBits input).length+1)^D

theorem combine_refinements (backend : RatBackend) (core : Bool) (data : DataInstruction)
    (semantic : StepRefinement backend core data) (resource : ResourceRefinement backend core data) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input data.val logical = some next →
        ∃ (run : List (State backend data)) (final : State backend data),
          ActualRun backend core data contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf data.val logical).toList) final.stk ∧
          run.length ≤ C*(Kernel.NatInstruction.dataSize contents+(encodeBits input).length+1)^D := by
  obtain ⟨C,D,positiveC,positiveD,bounded⟩ := resource
  refine ⟨C,D,positiveC,positiveD,?_⟩
  intro input logical next events contents size ready success
  obtain ⟨run,final,actual,represented⟩ := semantic input logical next events contents size ready success
  obtain ⟨known,knownFinal,knownActual,time⟩ := bounded input logical next events contents size ready success
  obtain ⟨same,_sameFinal⟩ := Kernel.Trace.final_unique (TM2.step (program backend core data))
    (before backend data contents) final knownFinal run known actual.1 actual.2.1 actual.2.2.1 actual.2.2.2
    knownActual.1 knownActual.2.1 knownActual.2.2.1 knownActual.2.2.2
  refine ⟨run,final,actual,represented,?_⟩
  rw [same]
  exact time

end PDROC.BitVM.VM.ISA
