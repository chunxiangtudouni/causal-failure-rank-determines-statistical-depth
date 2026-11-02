module

public import Paid.PDROC_D27Prepare_Assembly_001
public import Paid.PDROC_D27Prepare_Search_019
public import Paid.PDROC_D27Prepare_EndpointRun_008
public import Paid.PDROC_D27Prepare_ExponentRun_005
public import Paid.PDROC_D27Prepare_Q_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Assembly

/-- All three original searches and the original Q phase from raw6.
No initialized state, search answer, successful execution or bit certificate
is supplied by the caller. -/
theorem raw_search_trace (P : Parameters) (fee : ℚ) :
    ∃ (after : State) (trace : List State), Search.SearchFinished P fee after ∧
      after.output = [] ∧ trace.head? = some initial ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program (rawInput P fee) a = some b) ∧
      trace.length ≤ 600 + 29 * P.certificate.t0 + 120 * P.certificate.M + 40 * P.certificate.E ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) := by
  obtain ⟨beforeM, earlier, initialM, earlierOutput, earlierHead, earlierLast, earlierChain,
    earlierLength, earlierBounds⟩ := Search.raw_majority_trace P fee
  obtain ⟨beforeE, initialE, mSegment⟩ := EndpointRun.original_M_segment P fee (rawInput P fee) beforeM initialM
    (earlierBounds beforeM (List.mem_of_getLast? earlierLast))
  obtain ⟨beforeQ, initialQ, eSegment⟩ := ExponentRun.original_E_segment P fee (rawInput P fee) beforeE initialE mSegment.final_bounds
  obtain ⟨after, finished, qSegment⟩ := original_Q_segment P fee (rawInput P fee) beforeQ initialQ eSegment.final_bounds
  have mRegion : EndpointRun.region ⊆ Finset.range 64 := by
    intro address member
    simp only [EndpointRun.region, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have eRegion : ExponentRun.region ⊆ Finset.range 64 := by
    intro address member
    simp only [ExponentRun.region, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have qRegion : Q.region ⊆ Finset.range 64 := by
    intro address member
    simp only [Q.region, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have laterSegment := ((mSegment.widen_region mRegion).trans (eSegment.widen_region eRegion)).trans
    (qSegment.widen_region qRegion)
  obtain ⟨later, laterHead, laterLast, laterChain, laterLength, laterBounds, _⟩ := laterSegment.witness
  have indexBound : Search.majorityIndex P.certificate ≤ P.certificate.t0 := by
    have h := Search.t0_eq_two_mul_index_add_one P.certificate
    omega
  refine ⟨after, joinTrace earlier later, finished, laterSegment.output.trans earlierOutput,
    joinTrace_head earlier later initial beforeM earlierHead earlierLast laterHead,
    joinTrace_last earlier later after laterLast,
    joinTrace_chain program (rawInput P fee) earlier later beforeM earlierChain laterChain earlierLast laterHead,
    ?_, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late

end PDROC.D27Prepare.Assembly
