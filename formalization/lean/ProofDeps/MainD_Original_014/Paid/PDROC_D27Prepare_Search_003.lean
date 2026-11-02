module

public import Paid.PDROC_D27Prepare_Search_001
public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.D27Prepare.Search

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- Finite control induction on genuine fetched ISA fragments. The local
advance premise will be proved for the literal guard/update/jump pages;
it is not a successful-run or search oracle in the final preparation call. -/
theorem finite_loop_trace (program : Program) (input : List Cell)
    (invariant : ℕ → State → Prop) (good : State → Prop)
    (limit stepLength : ℕ)
    (invariantGood : ∀ i ≤ limit, ∀ state, invariant i state → good state)
    (advance : ∀ i < limit, ∀ before, invariant i before →
      ∃ (trace : List State) (after : State), trace.head? = some before ∧ trace.getLast? = some after ∧
        trace.IsChain (fun a b => step program input a = some b) ∧
        invariant (i + 1) after ∧ trace.length ≤ stepLength + 1 ∧
        ∀ state ∈ trace, good state) :
    ∀ remaining i, i + remaining = limit → ∀ before, invariant i before →
      ∃ (trace : List State) (after : State), trace.head? = some before ∧ trace.getLast? = some after ∧
        trace.IsChain (fun a b => step program input a = some b) ∧
        invariant limit after ∧ trace.length ≤ remaining * stepLength + 1 ∧
        ∀ state ∈ trace, good state := by
  intro remaining
  induction remaining with
  | zero =>
    intro i fits before inv
    have equal : i = limit := by omega
    subst i
    refine ⟨[before], before, rfl, rfl, .singleton before, inv, by simp, ?_⟩
    intro state member
    have equal : state = before := by simpa only [List.mem_singleton] using member
    subst state
    exact invariantGood limit le_rfl before inv
  | succ remaining ih =>
    intro i fits before inv
    have less : i < limit := by omega
    obtain ⟨first, middle, firstHead, firstLast, firstChain, nextInv, firstLength, firstGood⟩ :=
      advance i less before inv
    obtain ⟨later, after, laterHead, laterLast, laterChain, lastInv, laterLength, laterGood⟩ :=
      ih (i + 1) (by omega) middle nextInv
    refine ⟨joinTrace first later, after,
      joinTrace_head first later before middle firstHead firstLast laterHead,
      joinTrace_last first later after laterLast,
      joinTrace_chain program input first later middle firstChain laterChain firstLast laterHead,
      lastInv, ?_, ?_⟩
    · simp only [joinTrace, List.length_append, List.length_dropLast]
      rw [Nat.succ_mul]
      omega
    · intro state member
      rcases List.mem_append.mp member with early | late
      · exact firstGood state (List.mem_of_mem_dropLast early)
      · exact laterGood state late

/-- The bound is on the original primitiveTrace time of the actual
fetched chain, including its closing reached state. -/
theorem finite_loop_trace_time (program : Program) (input : List Cell)
    (invariant : ℕ → State → Prop) (good : State → Prop) (limit stepLength : ℕ)
    (invariantGood : ∀ i ≤ limit, ∀ state, invariant i state → good state)
    (advance : ∀ i < limit, ∀ before, invariant i before →
      ∃ (trace : List State) (after : State), trace.head? = some before ∧ trace.getLast? = some after ∧
        trace.IsChain (fun a b => step program input a = some b) ∧
        invariant (i + 1) after ∧ trace.length ≤ stepLength + 1 ∧
        ∀ state ∈ trace, good state)
    (remaining i : ℕ) (fits : i + remaining = limit) (before : State) (inv : invariant i before) :
    ∃ (trace : List State) (after : State), trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧ invariant limit after ∧
      time program trace ≤ 15 * (remaining * stepLength + 1) ∧
      ∀ state ∈ trace, good state := by
  obtain ⟨trace, after, head, last, chain, ended, length, safe⟩ :=
    finite_loop_trace program input invariant good limit stepLength invariantGood advance remaining i fits before inv
  exact ⟨trace, after, head, last, chain, ended,
    (time_le_length program trace).trans (Nat.mul_le_mul_left 15 length), safe⟩

end PDROC.D27Prepare.Search
