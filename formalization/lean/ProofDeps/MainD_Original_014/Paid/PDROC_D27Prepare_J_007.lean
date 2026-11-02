module

public import Paid.PDROC_D27Prepare_J_006
public import Paid.PDROC_D27Prepare_Q_007
public import Paid.PDROC_D27Prepare_HalveRun_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

/-- The actual positive-floor path39--44, including the optional ceiling
increment and the full logarithmic halving loop. It never unfolds the
possibly enormous integer ceiling into a unary iteration count. -/
theorem positive_budget_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (raw : Search.RawConstants P fee before) (location : before.pc = pc 39)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hL : Search.SlotHas before 11 (.rational P.Lambda))
    (hf : Search.SlotHas before 44 (.rational (P.positiveValueFloor fee)))
    (positive : 0 < P.positiveValueFloor fee) :
    ∃ (after : State) (trace : List State), after.pc = pc 45 ∧
      Search.SlotHas after 10 (.natural (P.bisectionBudget fee)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      trace.length ≤ 82 + 29 * P.bisectionBudget fee ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ address, address ∉ region → ∀ value, Search.SlotHas before address value → Search.SlotHas after address value) := by
  let memory : SlotMemory := ⟨before.heap, before.live⟩
  have matched : MemoryMatch before memory := ⟨rfl, rfl, raw.fresh⟩
  obtain ⟨ratioState, ratioMatch, ratioPc, ratioSegment⟩ := ratio_segment P fee input before memory
    matched location bounded raw.ratTwo hL raw.risk hf positive
  have ratioSlot : Search.SlotHas ratioState 45 (.rational (Budget.originalRatio P fee)) :=
    match_has ratioState _ 45 _ ratioMatch (Has.write_same _ _ _)
  have one40 := ratioSegment.final_frame.slot 14 (by decide) _ raw.natOne
  have encoding : ratEncodingBits (Budget.originalRatio P fee) + 1 ≤ operandBudget P fee := by
    have h := ratioSegment.final_bounds.heapValues 45 ratioSlot.1
    rw [ratioSlot.2] at h
    change 1 + ratEncodingBits (Budget.originalRatio P fee) ≤ operandBudget P fee at h
    omega
  obtain ⟨ceilState, ceilTrace, ceilPc, ceilSlot, ceilOutput, ceilFresh, ceilHead, ceilLast,
    ceilLength, ceilChain, ceilBounds, ceilFrames, _, _⟩ :=
    ceiling_pages_bounded region input 40 41 42 (by decide) (by decide) 45 46 (by decide)
      (by decide) (by decide) (by decide) (Budget.originalRatio P fee) (Budget.ratio_pos P fee positive).le
      rfl rfl ratioState ratioPc (ratioSegment.fresh.trans raw.fresh) ratioSlot one40
      (operandBudget P fee) ratioSegment.final_bounds (operandBudget_address_bits P fee) encoding
  have ceilSegment : Segment region input ratioState ceilState 64 (operandBudget P fee) 23 :=
    ⟨⟨ceilTrace, ceilHead, ceilLast, ceilChain, ceilLength, ceilBounds, ceilFrames⟩, ceilOutput, ceilFresh⟩
  have firstPair := ratioSegment.trans ceilSegment
  let ceilMemory : SlotMemory := ⟨ceilState.heap, ceilState.live⟩
  have ceilMatch : MemoryMatch ceilState ceilMemory := ⟨rfl, rfl, firstPair.fresh.trans raw.fresh⟩
  have zero42 := firstPair.final_frame.slot 13 (by decide) _ raw.natZero
  have one42 := firstPair.final_frame.slot 14 (by decide) _ raw.natOne
  obtain ⟨loopState, loopMatch, loopPc, setupSegment⟩ := halve_setup_segment P fee input ceilState ceilMemory
    ceilMatch ceilPc firstPair.final_bounds ceilSlot one42 zero42
  have prefixSegment := firstPair.trans setupSegment
  let loopMemory := halveInitial ceilMemory (Nat.ceil (Budget.originalRatio P fee))
  have loopValue : Has loopMemory 47 (.natural (Nat.ceil (Budget.originalRatio P fee) - 1)) :=
    Has.write_other _ 47 10 _ _ (Has.write_same _ _ _) (by decide)
  have loopCounter : Has loopMemory 10 (.natural 0) := Has.write_same _ _ _
  have toMemory (address : ℕ) (outside : address ∉ region) (value : Cell)
      (old : Search.SlotHas before address value) : Has loopMemory address value :=
    has_of_match loopState loopMemory address value loopMatch (prefixSegment.final_frame.slot address outside value old)
  obtain ⟨after, finalMemory, later, afterMatch, finalCounter, afterPc, laterOutput,
    laterHead, laterLast, laterLength, laterChain, laterBounds, preserves⟩ :=
    HalveRun.original_loop_trace input P fee loopState loopMemory loopMatch loopPc prefixSegment.final_bounds
      (toMemory 13 (by decide) _ raw.natZero) loopValue loopCounter
      (toMemory 15 (by decide) _ raw.natTwo) (toMemory 14 (by decide) _ raw.natOne)
  obtain ⟨earlier, earlierHead, earlierLast, earlierChain, earlierLength, earlierBounds, _⟩ := prefixSegment.witness
  refine ⟨after, joinTrace earlier later, afterPc, match_has after finalMemory 10 _ afterMatch finalCounter,
    laterOutput.trans prefixSegment.output, afterMatch.base.trans raw.fresh.symm,
    joinTrace_head earlier later before loopState earlierHead earlierLast laterHead,
    joinTrace_last earlier later after laterLast,
    joinTrace_chain program input earlier later loopState earlierChain laterChain earlierLast laterHead,
    ?_, ?_, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast]
    change earlier.length ≤ 73 at earlierLength
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late
  · intro address outside value old
    apply match_has after finalMemory address value afterMatch
    apply preserves address
    · intro same
      exact outside (same.symm ▸ (by decide : 47 ∈ region))
    · intro same
      exact outside (same.symm ▸ (by decide : 10 ∈ region))
    · exact toMemory address outside value old

end PDROC.D27Prepare.J
