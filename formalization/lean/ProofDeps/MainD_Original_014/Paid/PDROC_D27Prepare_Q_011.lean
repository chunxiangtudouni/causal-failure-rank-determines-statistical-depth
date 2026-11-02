module

public import Paid.PDROC_D27Prepare_Q_010
public import Paid.PDROC_D27Prepare_Q_005
public import Paid.PDROC_D27Prepare_Q_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

/-- Complete actual Q phase: both rational ceilings, both optional
increments and both max branches. No value for Q or successful execution
is supplied by the caller; every physical state has the same bit bound. -/
theorem original_Q_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : QInitial P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, Search.SearchFinished P fee after ∧
      Segment region input before after 64 (operandBudget P fee) 138 := by
  obtain ⟨firstSetup, firstTrace, firstPc, firstValueSlot, firstOutput, firstFresh,
    firstHead, firstLast, firstLength, firstChain, firstBounds, firstFrames, _, _⟩ :=
    first_setup_trace P fee input before initial.raw initial.location initial.M bounded
  have firstSegment : Segment region input before firstSetup 64 (operandBudget P fee) 29 :=
    ⟨⟨firstTrace, firstHead, firstLast, firstChain, firstLength.le, firstBounds, firstFrames⟩,
      firstOutput, firstFresh⟩
  have firstRaw := progress_raw P fee before firstSetup initial.raw firstSegment.final_frame firstFresh
  have firstEncoding : ratEncodingBits (firstValue P) + 1 ≤ operandBudget P fee := by
    have h := firstSegment.final_bounds.heapValues 32 firstValueSlot.1
    rw [firstValueSlot.2] at h
    change 1 + ratEncodingBits (firstValue P) ≤ operandBudget P fee at h
    omega
  obtain ⟨firstCeil, firstCeilTrace, firstCeilPc, firstCeilSlot, firstCeilOutput, firstCeilFresh,
    firstCeilHead, firstCeilLast, firstCeilLength, firstCeilChain, firstCeilBounds,
    firstCeilFrames, _, _⟩ :=
    ceiling_pages_bounded region input 11 12 13 (by decide) (by decide) 32 52
      (by decide) (by decide) (by decide) (by decide) (firstValue P) (firstValue_nonnegative P)
      rfl rfl firstSetup firstPc firstRaw.fresh firstValueSlot firstRaw.natOne
      (operandBudget P fee) firstSegment.final_bounds (operandBudget_address_bits P fee) firstEncoding
  have firstCeilSegment : Segment region input firstSetup firstCeil 64 (operandBudget P fee) 23 :=
    ⟨⟨firstCeilTrace, firstCeilHead, firstCeilLast, firstCeilChain, firstCeilLength,
      firstCeilBounds, firstCeilFrames⟩, firstCeilOutput, firstCeilFresh⟩
  have firstPair := firstSegment.trans firstCeilSegment
  have rawAt13 := progress_raw P fee before firstCeil initial.raw firstPair.final_frame firstPair.fresh
  have exponent := progress_slot before firstCeil firstPair.final_frame 8 (by decide) _ initial.E
  have gammaSquare := progress_slot before firstCeil firstPair.final_frame 24 (by decide) _ initial.gammaSquared
  obtain ⟨secondSetup, secondTrace, secondPc, secondValueSlot, secondOutput, secondFresh,
    secondHead, secondLast, secondLength, secondChain, secondBounds, secondFrames, secondHeap, secondLive⟩ :=
    second_setup_trace P fee input firstCeil rawAt13 firstCeilPc exponent gammaSquare firstPair.final_bounds
  have secondSegment : Segment region input firstCeil secondSetup 64 (operandBudget P fee) 29 :=
    ⟨⟨secondTrace, secondHead, secondLast, secondChain, secondLength.le, secondBounds, secondFrames⟩,
      secondOutput, secondFresh⟩
  have firstCeilAt14 : Search.SlotHas secondSetup 52 (.natural (Nat.ceil (firstValue P))) := by
    constructor
    · rw [secondLive]; exact Finset.mem_insert_of_mem firstCeilSlot.1
    · rw [secondHeap, Function.update_of_ne (by decide : 52 ≠ 32)]; exact firstCeilSlot.2
  have secondRaw := progress_raw P fee firstCeil secondSetup rawAt13 secondSegment.final_frame secondFresh
  have secondEncoding : ratEncodingBits (secondValue P) + 1 ≤ operandBudget P fee := by
    have h := secondSegment.final_bounds.heapValues 32 secondValueSlot.1
    rw [secondValueSlot.2] at h
    change 1 + ratEncodingBits (secondValue P) ≤ operandBudget P fee at h
    omega
  obtain ⟨secondCeil, secondCeilTrace, secondCeilPc, secondCeilSlot, secondCeilOutput, secondCeilFresh,
    secondCeilHead, secondCeilLast, secondCeilLength, secondCeilChain, secondCeilBounds,
    secondCeilFrames, secondCeilHeap, secondCeilLive⟩ :=
    ceiling_pages_bounded region input 14 15 16 (by decide) (by decide) 32 53
      (by decide) (by decide) (by decide) (by decide) (secondValue P) (secondValue_nonnegative P)
      rfl rfl secondSetup secondPc secondRaw.fresh secondValueSlot secondRaw.natOne
      (operandBudget P fee) secondSegment.final_bounds (operandBudget_address_bits P fee) secondEncoding
  have secondCeilSegment : Segment region input secondSetup secondCeil 64 (operandBudget P fee) 23 :=
    ⟨⟨secondCeilTrace, secondCeilHead, secondCeilLast, secondCeilChain, secondCeilLength,
      secondCeilBounds, secondCeilFrames⟩, secondCeilOutput, secondCeilFresh⟩
  have prefix16 := (firstPair.trans secondSegment).trans secondCeilSegment
  have firstCeilAt16 : Search.SlotHas secondCeil 52 (.natural (Nat.ceil (firstValue P))) := by
    constructor
    · rw [secondCeilLive]; exact Finset.mem_insert_of_mem firstCeilAt14.1
    · rw [secondCeilHeap, Function.update_of_ne (by decide : 52 ≠ 53)]; exact firstCeilAt14.2
  have raw16 := progress_raw P fee before secondCeil initial.raw prefix16.final_frame prefix16.fresh
  obtain ⟨after, afterPc, afterValue, finalSegment⟩ := select_Q_segment P fee input secondCeil
    secondCeilPc raw16.fresh (Nat.ceil (firstValue P)) (Nat.ceil (secondValue P))
    firstCeilAt16 secondCeilSlot raw16.natOne prefix16.final_bounds
  have segment := prefix16.trans finalSegment
  have value : Search.SlotHas after 9 (.natural P.certificate.Q) := by
    simpa only [CertificateInput.Q, firstValue, secondValue] using afterValue
  exact ⟨after, finish_of_progress P fee before after initial segment.final_frame afterPc segment.fresh value,
    segment⟩

end PDROC.D27Prepare.Q
