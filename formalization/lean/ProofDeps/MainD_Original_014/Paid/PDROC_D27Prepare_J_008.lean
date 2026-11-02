module

public import Paid.PDROC_D27Prepare_J_004
public import Paid.PDROC_D27Prepare_J_007
public import Paid.PDROC_D27Prepare_FloorBounds_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

/-- Complete original pages32--44. The fee=0/min branch computes the
first floor, the signed test computes the positive floor, and the actual
J path either writes zero or runs the ceiling/halving machine. -/
theorem original_budget_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (raw : Search.RawConstants P fee before) (location : before.pc = pc 32)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hL : Search.SlotHas before 11 (.rational P.Lambda))
    (hz : Search.SlotHas before 12 (.rational (P.zeroChargeRisk fee))) :
    ∃ (after : State) (trace : List State), after.pc = pc 45 ∧
      Search.SlotHas after 10 (.natural (P.bisectionBudget fee)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      trace.length ≤ 160 + 29 * P.bisectionBudget fee ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ address, address ∉ region → ∀ value, Search.SlotHas before address value → Search.SlotHas after address value) := by
  obtain ⟨floorState, floorRaw, floorPc, firstFloor, first0⟩ :=
    first_floor_segment P fee input before raw location bounded
  have first : Segment region input before floorState 64 (operandBudget P fee) 26 :=
    first0.widen_region (by intro address member; simpa only [Finset.mem_singleton.mp member] using (by decide : 43 ∈ region))
  have zeta37 := first.final_frame.slot 12 (by decide) _ hz
  let memory : SlotMemory := ⟨floorState.heap, floorState.live⟩
  have matched : MemoryMatch floorState memory := ⟨rfl, rfl, floorRaw.fresh⟩
  obtain ⟨signedState, signedTrace, signedMatch, signedPc, signedOutput, signedHead,
    signedLast, signedLength, signedChain, signedBounds, signedFrames⟩ :=
    FloorBounds.signed_floor_bounded input P fee floorState memory matched floorPc first.final_bounds
      zeta37 floorRaw.risk firstFloor floorRaw.ratZero
  have signed : Segment {32, 44} input floorState signedState 64 (operandBudget P fee) 29 :=
    ⟨⟨signedTrace, signedHead, signedLast, signedChain, signedLength.le, signedBounds, signedFrames⟩,
      signedOutput, signedMatch.base.trans floorRaw.fresh.symm⟩
  have signedWide : Segment region input floorState signedState 64 (operandBudget P fee) 29 :=
    signed.widen_region (by intro address member; simp only [Finset.mem_insert, Finset.mem_singleton] at member; rcases member with rfl | rfl <;> decide)
  have firstPair := first.trans signedWide
  have signedRaw := Search.RawConstants.transport P fee before signedState raw
    (by
      intro address read
      apply firstPair.final_frame.1.1 address
      simp only [region, Finset.mem_insert, Finset.mem_singleton]
      omega)
    firstPair.final_frame.2 firstPair.fresh
  have signedFloor : Search.SlotHas signedState 44 (.rational (P.positiveValueFloor fee)) :=
    match_has signedState _ 44 _ signedMatch (Has.write_same _ _ _)
  have signedLambda := firstPair.final_frame.slot 11 (by decide) _ hL
  by_cases positive : 0 < P.positiveValueFloor fee
  · have at39 : signedState.pc = pc 39 := by simpa [Comparison.rat, positive] using signedPc
    obtain ⟨after, later, afterPc, counter, laterOutput, laterFresh, laterHead, laterLast,
      laterChain, laterLength, laterBounds, laterPreserves⟩ :=
      positive_budget_trace P fee input signedState signedRaw at39 firstPair.final_bounds signedLambda signedFloor positive
    obtain ⟨earlier, earlierHead, earlierLast, earlierChain, earlierLength, earlierBounds, _⟩ := firstPair.witness
    refine ⟨after, joinTrace earlier later, afterPc, counter, laterOutput.trans firstPair.output,
      laterFresh.trans firstPair.fresh,
      joinTrace_head earlier later before signedState earlierHead earlierLast laterHead,
      joinTrace_last earlier later after laterLast,
      joinTrace_chain program input earlier later signedState earlierChain laterChain earlierLast laterHead,
      ?_, ?_, ?_⟩
    · change earlier.length ≤ 55 at earlierLength
      simp only [joinTrace, List.length_append, List.length_dropLast]
      omega
    · intro state member
      rcases List.mem_append.mp member with early | late
      · exact earlierBounds state (List.mem_of_mem_dropLast early)
      · exact laterBounds state late
    · intro address outside value old
      exact laterPreserves address outside value (firstPair.final_frame.slot address outside value old)
  · have at38 : signedState.pc = pc 38 := by simpa [Comparison.rat, positive] using signedPc
    obtain ⟨after, afterPc, value, lastSegment⟩ := copy_page_segment region input (operandBudget P fee)
      38 45 13 10 (by decide) rfl (by decide) (by decide) (by decide) signedState at38
      signedRaw.fresh (.natural 0) signedRaw.natZero firstPair.final_bounds (operandBudget_address_bits P fee)
    have counter : Search.SlotHas after 10 (.natural (P.bisectionBudget fee)) := by
      simpa only [Budget.budget_zero_of_floor_nonpositive P fee (le_of_not_gt positive)] using value
    have complete := firstPair.trans lastSegment
    obtain ⟨trace, head, last, chain, length, bounds, _⟩ := complete.witness
    exact ⟨after, trace, afterPc, counter, complete.output, complete.fresh,
      head, last, chain, length.trans (by omega), bounds,
      fun address outside cell old => complete.final_frame.slot address outside cell old⟩

end PDROC.D27Prepare.J
