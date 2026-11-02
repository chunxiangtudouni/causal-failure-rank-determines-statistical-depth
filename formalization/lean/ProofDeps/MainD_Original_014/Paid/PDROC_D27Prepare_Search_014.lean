module

public import Paid.PDROC_D27Prepare_Search_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Search

open Program Resources

/-- The complete original majority loop, including its successful guard
and branch. Its iteration count is the original least odd t0, rather
than a supplied execution oracle or an extra stopping assumption. -/
theorem majority_loop_trace (input : List Cell) (P : Parameters) (fee : ℚ)
    (remaining j : ℕ) (fits : j + remaining = majorityIndex P.certificate)
    (before : State) (ready : MajorityReady P.certificate j before)
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), after.pc = pc 4 ∧
      after.register .fresh = .natural 0 ∧ SlotHas after 6 (.natural P.certificate.t0) ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      trace.length ≤ remaining * 29 + 9 ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      after.live = before.live ∧ after.output = before.output ∧
      (∀ address, address ≠ 6 → address ≠ 28 → after.heap address = before.heap address) := by
  obtain ⟨middle, earlier, middleReady, earlierHead, earlierLast, earlierChain,
    earlierLength, earlierBounds, middleLive, middleOutput, middleHeap⟩ :=
    majority_rejected_loop input P fee remaining j fits before ready bounded
  obtain ⟨after, later, laterHead, laterLast, laterLength, laterChain, afterPc,
    afterHeap, afterLive, afterFresh, afterOutput, prefixes, afterShape⟩ :=
    majority_guard_page_trace input P.certificate (majorityIndex P.certificate) le_rfl middle
      middleReady.location middleReady.fresh middleReady.power middleReady.threshold
  have middleBound := earlierBounds middle (List.mem_of_getLast? earlierLast)
  have enough : 2 ≤ operandBudget P fee := by
    have h := linear_le_operandBudget P fee
    omega
  have prefixBits := ratCompareSlots_prefix_bounds input middle 28 27 64 (operandBudget P fee) .lessEqual
    (P.certificate.varianceBase ^ (2 * majorityIndex P.certificate + 1))
    ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2)
    middleBound middleReady.fresh middleReady.power.1 middleReady.threshold.1
    middleReady.power.2 middleReady.threshold.2 (by decide) (by decide)
    (operandBudget_address_bits P fee) enough
  have executed := ratCompareSlots_execute input middle 0 28 27
    (P.certificate.varianceBase ^ (2 * majorityIndex P.certificate + 1))
    ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2) .lessEqual
    middleReady.fresh middleReady.power.1 middleReady.threshold.1 middleReady.power.2 middleReady.threshold.2
  have finalBound : StateBounds 64 (operandBudget P fee) after := by
    rw [afterShape]
    exact (prefixBits.final executed).with_pc _
  have laterBounds : ∀ state ∈ later, StateBounds 64 (operandBudget P fee) state := by
    intro state member
    rcases prefixes state member with same | ⟨count, _, actual⟩
    · simpa only [same] using finalBound
    · exact prefixBits count state actual
  have counter : SlotHas after 6 (.natural P.certificate.t0) := by
    constructor
    · rw [afterLive]; exact middleReady.counter.1
    · rw [afterHeap]
      simpa only [t0_eq_two_mul_index_add_one P.certificate] using middleReady.counter.2
  refine ⟨after, joinTrace earlier later, by simpa only [↓reduceIte] using afterPc,
    afterFresh.trans middleReady.fresh, counter,
    joinTrace_head earlier later before middle earlierHead earlierLast laterHead,
    joinTrace_last earlier later after laterLast,
    joinTrace_chain program input earlier later middle earlierChain laterChain earlierLast laterHead,
    ?_, ?_, afterLive.trans middleLive, afterOutput.trans middleOutput, ?_⟩
  · have nonempty : earlier ≠ [] := by
      intro empty
      simp only [empty, List.head?_nil] at earlierHead
      cases earlierHead
    have positive : 0 < earlier.length := List.length_pos_iff.mpr nonempty
    simp only [joinTrace, List.length_append, List.length_dropLast, laterLength]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late
  · intro address notCounter notPower
    rw [afterHeap]
    exact middleHeap address notCounter notPower

end PDROC.D27Prepare.Search
