module

public import Paid.PDROC_D27Prepare_Dyadic_004
public import Paid.PDROC_D27Prepare_Dyadic_002
public import Paid.PDROC_D27Prepare_J_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Dyadic

/-- Original page21 setup and the complete N-step dyadic loop. Lambda
and 2^-N are computed from the actual search result and raw constants. -/
theorem original_lambda_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : Search.SearchFinished P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), after.pc = pc 24 ∧
      Search.SlotHas after 11 (.rational P.Lambda) ∧
      Search.SlotHas after 39 (.rational ((1 / 2 : ℚ) ^ P.certificate.stages)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      trace.length ≤ 64 + 29 * P.certificate.stages ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ address, address ∉ region → ∀ value, Search.SlotHas before address value → Search.SlotHas after address value) := by
  obtain ⟨initialized, initMatch, initPc, setupSegment⟩ := setup_segment P fee input before initial bounded
  let memory := multiplierNext (Search.currentMemory before) P
  have carry (address : ℕ) (outside : address ∉ region) (value : Cell)
      (stored : Search.SlotHas before address value) : Has memory address value :=
    has_of_match initialized memory address value initMatch
      (MemoryProgress.slot setupSegment.final_frame address outside value stored)
  have zero : Has memory 35 (.natural 0) := by simp [memory, multiplierNext, Has, SlotMemory.write]
  have one : Has memory 39 (.rational 1) := Has.write_same _ _ _
  have lambda : Has memory 11 (.rational P.Lambda) := by simp [memory, multiplierNext, Has, SlotMemory.write]
  obtain ⟨after, finalMemory, later, afterMatch, finalIndex, finalPower, afterPc, output,
    head, last, length, chain, bounds, preserves⟩ := original_loop_trace input P fee initialized memory initMatch initPc
      setupSegment.final_bounds (carry 0 (by decide) _ initial.raw.stages) zero
      (carry 14 (by decide) _ initial.raw.natOne) (carry 21 (by decide) _ initial.raw.ratHalf) one
  have finalLambda : Has finalMemory 11 (.rational P.Lambda) := preserves 11 (by decide) (by decide) _ lambda
  obtain ⟨earlier, earlierHead, earlierLast, earlierChain, earlierLength, earlierBounds, _⟩ := setupSegment.witness
  refine ⟨after, joinTrace earlier later, afterPc,
    match_has after finalMemory 11 _ afterMatch finalLambda, match_has after finalMemory 39 _ afterMatch finalPower,
    output.trans setupSegment.output, afterMatch.base.trans initial.raw.fresh.symm,
    joinTrace_head earlier later before initialized earlierHead earlierLast head,
    joinTrace_last earlier later after last,
    joinTrace_chain program input earlier later initialized earlierChain chain earlierLast head,
    ?_, ?_, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact bounds state late
  · intro address outside value stored
    apply match_has after finalMemory address value afterMatch
    apply preserves address
    · intro same
      exact outside (same.symm ▸ (by decide : 35 ∈ region))
    · intro same
      exact outside (same.symm ▸ (by decide : 39 ∈ region))
    · exact carry address outside value stored

end PDROC.D27Prepare.Dyadic
