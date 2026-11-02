module

public import Paid.PDROC_D27Prepare_Assembly_002
public import Paid.PDROC_D27Prepare_Assembly_003
public import Paid.PDROC_D27Prepare_Assembly_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

/-- The real state immediately before the original thirteen emits.  Its
heap is the prepared row and its output is still empty. -/
theorem raw_preFinal_trace (P : Parameters) (fee : ℚ) :
    ∃ (after : State) (trace : List State), PreFinalState P fee after ∧
      trace.head? = some initial ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program (rawInput P fee) a = some b) ∧
      trace.length ≤ 1000 + 29 * P.certificate.t0 + 120 * P.certificate.M +
        40 * P.certificate.E + 129 * P.certificate.stages + 29 * P.bisectionBudget fee ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) := by
  obtain ⟨middle, earlier, finished, empty, earlierHead, earlierLast, earlierChain,
    earlierLength, earlierBounds⟩ := raw_search_trace P fee
  obtain ⟨after, later, preFinal, laterHead, laterLast, laterChain, laterLength, laterBounds⟩ :=
    search_to_preFinal_trace P fee (rawInput P fee) middle finished empty
      (earlierBounds middle (List.mem_of_getLast? earlierLast))
  refine ⟨after, joinTrace earlier later, preFinal,
    joinTrace_head earlier later initial middle earlierHead earlierLast laterHead,
    joinTrace_last earlier later after laterLast,
    joinTrace_chain program (rawInput P fee) earlier later middle earlierChain laterChain earlierLast laterHead,
    ?_, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late

end PDROC.D27Prepare.Assembly
