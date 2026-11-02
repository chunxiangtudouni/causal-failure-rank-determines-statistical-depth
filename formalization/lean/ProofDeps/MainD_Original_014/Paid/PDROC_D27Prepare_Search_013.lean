module

public import Paid.PDROC_D27Prepare_Search_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Search

/-- All rejected candidates of the original least-odd majority search.
Each transition is fetched from the one fixed program, with a single
operand envelope covering every register and live heap cell throughout.
The terminal successful guard is handled by the following exit page. -/
theorem majority_rejected_loop (input : List Cell) (P : Parameters) (fee : ℚ)
    (remaining j : ℕ) (fits : j + remaining = majorityIndex P.certificate)
    (before : State) (ready : MajorityReady P.certificate j before)
    (bounded : Resources.StateBounds 64 (Resources.operandBudget P fee) before) :
    ∃ (after : State) (trace : List State),
      MajorityReady P.certificate (majorityIndex P.certificate) after ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      trace.length ≤ remaining * 29 + 1 ∧
      (∀ state ∈ trace, Resources.StateBounds 64 (Resources.operandBudget P fee) state) ∧
      after.live = before.live ∧ after.output = before.output ∧
      (∀ address, address ≠ 6 → address ≠ 28 → after.heap address = before.heap address) := by
  let invariant (i : ℕ) (state : State) : Prop :=
    MajorityReady P.certificate i state ∧
      Resources.StateBounds 64 (Resources.operandBudget P fee) state ∧
      state.live = before.live ∧ state.output = before.output ∧
      (∀ address, address ≠ 6 → address ≠ 28 → state.heap address = before.heap address)
  let good (state : State) : Prop := Resources.StateBounds 64 (Resources.operandBudget P fee) state
  have initialInvariant : invariant j before :=
    ⟨ready, bounded, rfl, rfl, fun _ _ _ => rfl⟩
  have advance : ∀ i < majorityIndex P.certificate, ∀ first, invariant i first →
      ∃ (trace : List State) (after : State), trace.head? = some first ∧ trace.getLast? = some after ∧
        trace.IsChain (fun a b => step Program.program input a = some b) ∧
        invariant (i + 1) after ∧ trace.length ≤ 29 + 1 ∧
        ∀ state ∈ trace, good state := by
    intro i inside first inv
    obtain ⟨after, trace, head, last, length, chain, afterReady, heap, live, output, allBounds⟩ :=
      majority_iteration_bounded_trace input P fee i inside first inv.1 inv.2.1
    have afterBound := allBounds after (List.mem_of_getLast? last)
    refine ⟨trace, after, head, last, chain, ?_, by omega, allBounds⟩
    refine ⟨afterReady, afterBound, live.trans inv.2.2.1, output.trans inv.2.2.2.1, ?_⟩
    intro address notCounter notPower
    rw [heap, Function.update_of_ne notPower, Function.update_of_ne notCounter]
    exact inv.2.2.2.2 address notCounter notPower
  obtain ⟨trace, after, head, last, chain, ended, length, allBounds⟩ :=
    finite_loop_trace Program.program input invariant good (majorityIndex P.certificate) 29
      (fun _ _ _ inv => inv.2.1) advance remaining j fits before initialInvariant
  exact ⟨after, trace, ended.1, head, last, chain, length, allBounds,
    ended.2.2.1, ended.2.2.2.1, ended.2.2.2.2⟩

end PDROC.D27Prepare.Search
