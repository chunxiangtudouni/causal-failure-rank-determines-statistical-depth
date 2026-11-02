module

public import Paid.PDROC_BitVM_VM_Phases_Calls_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Calls

open Turing PaperProofs.Paid.Computation

def Finalized (cells : List Cell) (contents data : ISA.Stack → List Bool) : Prop :=
  data 0 = encodeBits cells ∧ data 22 = [] ∧ data 24 = [] ∧ data 23 = [] ∧
    ∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → data other = contents other

/-- The output word/ticks are read from the actual physical stacks.
One real Finalize002 path creates encodeBits on0; no host output list
is inserted into the caller's tape. Its outside frame and old-data cost
are transported along this exact selected call, with all PiSaved intact. -/
theorem finalize_call (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (cells : List Cell) (contents : ISA.Stack → List Bool)
    (outputWord : contents 22 = (cells.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate cells.length true) :
    CallerRun backend prepareCode coreCode (finalizePhase core) store contents
      (Finalized cells contents) (Codec.Finalize.timeBudget contents) := by
  obtain ⟨run, final, head, chain, last, halt, done, encoded, output, scratch, ticks, frame, time, projected, space⟩ :=
    Codec.Finalize.runs_resources cells contents default outputWord outputTicks
  have original : ∃ (selected : List Codec.Finalize.State) (returned : Codec.Finalize.State),
      selected.head? = some (Codec.Finalize.before contents default) ∧
      selected.IsChain (fun a b => TM2.step Codec.Finalize.program a = some b) ∧
      selected.getLast? = some returned ∧ TM2.step Codec.Finalize.program returned = none ∧
      Finalized cells contents returned.stk ∧ selected.length ≤ Codec.Finalize.timeBudget contents :=
    ⟨run, final, head, chain, last, halt, ⟨encoded, output, scratch, ticks, frame⟩, time⟩
  have callee : LocalRun backend prepareCode coreCode (finalizePhase core) contents
      (Finalized cells contents) (Codec.Finalize.timeBudget contents) := by
    cases core <;> exact original
  exact local_to_caller backend prepareCode coreCode (finalizePhase core) store contents _ _ callee

/-- The existing actual source-run observer supplies cells and ticks.
In particular prepare's thirteen cells must come from its real output;
this adapter never overrides the subsequently remounted readonly bank. -/
theorem finalize_observables (backend : ISA.RatBackend) (prepareCode coreCode : Program) (core : Bool)
    (store : Store backend prepareCode coreCode) (input : List Cell)
    (logical : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent) (contents : ISA.Stack → List Bool)
    (observed : Source.Observables input logical events contents) :
    CallerRun backend prepareCode coreCode (finalizePhase core) store contents
      (Finalized logical.output contents) (Codec.Finalize.timeBudget contents) :=
  finalize_call backend prepareCode coreCode core store logical.output contents observed.outputWord observed.outputTicks

end PDROC.BitVM.VM.Phases.Calls
