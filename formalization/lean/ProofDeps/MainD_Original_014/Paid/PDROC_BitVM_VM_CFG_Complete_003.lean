module

public import Paid.PDROC_BitVM_VM_CFG_Complete_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Complete

open Turing PaperProofs.Paid.Computation

/-- An explicit TM2 trace is extracted from the SAME complete_path
witness, never from a second existential simulation. Its final logical
observer and exact event history refer to that very terminal config. -/
theorem complete_trace (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (input : List Cell) (states : List PaperProofs.Paid.Computation.State)
        (logicalFinal : PaperProofs.Paid.Computation.State) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Runs code input states logicalFinal →
        Source.Ready input PaperProofs.Paid.Computation.initial [] contents →
        ∃ (trace : List (Program.State backend code)) (terminal : Program.State backend code),
          trace.head? = some (Program.before backend code contents) ∧
          trace.IsChain (fun a b => TM2.step (Program.program backend core code) a = some b) ∧
          trace.getLast? = some terminal ∧ TM2.step (Program.program backend core code) terminal = none ∧
          Source.Ready input logicalFinal (BoundaryBudget.actualHistory code states) terminal.stk ∧
          trace.length ≤ totalBudget C d code input states + 1 := by
  obtain ⟨C, d, positiveC, positiveD, chosen⟩ := complete_path backend core code
  refine ⟨C, d, positiveC, positiveD, ?_⟩
  intro input states logicalFinal contents size actual ready
  obtain ⟨terminal, halted, represented, path, clock⟩ := chosen input states logicalFinal contents size actual ready
  let trace := Program.before backend code contents :: path.posts
  refine ⟨trace, terminal, rfl, path.chain, path.last, halted, represented, ?_⟩
  change path.posts.length + 1 ≤ totalBudget C d code input states + 1
  omega

end PDROC.BitVM.VM.CFG.Complete
