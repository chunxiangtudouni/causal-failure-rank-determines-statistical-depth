module

public import Paid.PDROC_D27Prepare_Search_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

namespace PDROC.D27Prepare.Search

theorem majority_guard_boolean (D : CertificateInput) (j : ℕ)
    (range : j ≤ majorityIndex D) :
    Comparison.rat .lessEqual (D.varianceBase ^ (2 * j + 1))
      ((D.risk / (2 * (D.stages : ℚ))) ^ 2) = decide (j = majorityIndex D) := by
  change decide (D.varianceBase ^ (2 * j + 1) ≤ (D.risk / (2 * (D.stages : ℚ))) ^ 2) = _
  exact decide_eq_decide.mpr (majority_guard_iff D j range)

theorem endpoint_guard_boolean (D : CertificateInput) (m : ℕ) (range : m ≤ D.M) :
    Comparison.rat .lessEqual 1 (D.menuRatio * (1 + D.odds ^ m)) = decide (m = D.M) := by
  change decide ((1 : ℚ) ≤ D.menuRatio * (1 + D.odds ^ m)) = _
  exact decide_eq_decide.mpr (endpoint_guard_eq_iff D m range)

theorem exponent_guard_boolean (D : CertificateInput) (e : ℕ)
    (positive : 1 ≤ e) (range : e ≤ D.E) :
    Comparison.rat .lessEqual ((1 / 2 : ℚ) ^ e) (D.gamma * D.epsilon) = decide (e = D.E) := by
  change decide ((1 / 2 : ℚ) ^ e ≤ D.gamma * D.epsilon) = _
  exact decide_eq_decide.mpr (exponent_guard_iff D e positive range)

/-- The majority guard is an actual eight-instruction fetched page. It
exits exactly at the original least positive odd t0. -/
theorem majority_guard_page_trace (input : List Cell) (D : CertificateInput) (j : ℕ)
    (range : j ≤ majorityIndex D) (before : State) (location : before.pc = Program.pc 2)
    (fresh : before.register .fresh = .natural 0)
    (power : SlotHas before 28 (.rational (D.varianceBase ^ (2 * j + 1))))
    (threshold : SlotHas before 27 (.rational ((D.risk / (2 * (D.stages : ℚ))) ^ 2))) :
    ∃ (after : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some after ∧ trace.length = 9 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.pc = (if j = majorityIndex D then Program.pc 4 else Program.pc 3) ∧
      after.heap = before.heap ∧ after.live = before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ 7,
        linearExecute input ((Program.majorityGuard).take count) before = some state) ∧
      after = {Program.comparisonResult before 0 28 27
        (Comparison.rat .lessEqual (D.varianceBase ^ (2 * j + 1))
          ((D.risk / (2 * (D.stages : ℚ))) ^ 2)) with
        pc := if j = majorityIndex D then Program.pc 4 else Program.pc 3} := by
  let middle := Program.comparisonResult before 0 28 27
    (Comparison.rat .lessEqual (D.varianceBase ^ (2 * j + 1))
      ((D.risk / (2 * (D.stages : ℚ))) ^ 2))
  let after := {middle with pc := if (Comparison.rat .lessEqual (D.varianceBase ^ (2 * j + 1))
      ((D.risk / (2 * (D.stages : ℚ))) ^ 2)) then (Program.pc 4) else (Program.pc 3)}
  obtain ⟨trace, head, last, length, chain, heap, live, base, output, prefixes⟩ :=
    rat_compare_page_trace input 2 (by decide) before location .lessEqual 28 27 3 4
      (D.varianceBase ^ (2 * j + 1)) ((D.risk / (2 * (D.stages : ℚ))) ^ 2)
      rfl fresh power threshold
  refine ⟨after, trace, head, last, length, chain, ?_, heap, live, base, output, prefixes, ?_⟩
  · simp only [after, majority_guard_boolean D j range, decide_eq_true_eq]
  · change after = {middle with pc := if j = majorityIndex D then Program.pc 4 else Program.pc 3}
    simp only [after, majority_guard_boolean D j range, decide_eq_true_eq]

/-- The dyadic exponent page exits exactly at the original Nat.find E. -/
theorem exponent_guard_page_trace (input : List Cell) (D : CertificateInput) (e : ℕ)
    (positive : 1 ≤ e) (range : e ≤ D.E) (before : State)
    (location : before.pc = Program.pc 8) (fresh : before.register .fresh = .natural 0)
    (power : SlotHas before 28 (.rational ((1 / 2 : ℚ) ^ e)))
    (threshold : SlotHas before 31 (.rational (D.gamma * D.epsilon))) :
    ∃ (after : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some after ∧ trace.length = 9 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      after.pc = (if e = D.E then Program.pc 10 else Program.pc 9) ∧
      after.heap = before.heap ∧ after.live = before.live ∧
      after.register .fresh = before.register .fresh ∧ after.output = before.output ∧
      (∀ state ∈ trace, state = after ∨ ∃ count ≤ 7,
        linearExecute input ((Program.exponentGuard).take count) before = some state) ∧
      after = {Program.comparisonResult before 0 28 31
        (Comparison.rat .lessEqual ((1 / 2 : ℚ) ^ e) (D.gamma * D.epsilon)) with
        pc := if e = D.E then Program.pc 10 else Program.pc 9} := by
  let middle := Program.comparisonResult before 0 28 31
    (Comparison.rat .lessEqual ((1 / 2 : ℚ) ^ e) (D.gamma * D.epsilon))
  let after := {middle with pc := if (Comparison.rat .lessEqual ((1 / 2 : ℚ) ^ e)
      (D.gamma * D.epsilon)) then (Program.pc 10) else (Program.pc 9)}
  obtain ⟨trace, head, last, length, chain, heap, live, base, output, prefixes⟩ :=
    rat_compare_page_trace input 8 (by decide) before location .lessEqual 28 31 9 10
      ((1 / 2 : ℚ) ^ e) (D.gamma * D.epsilon) rfl fresh power threshold
  refine ⟨after, trace, head, last, length, chain, ?_, heap, live, base, output, prefixes, ?_⟩
  · simp only [after, exponent_guard_boolean D e positive range, decide_eq_true_eq]
  · change after = {middle with pc := if e = D.E then Program.pc 10 else Program.pc 9}
    simp only [after, exponent_guard_boolean D e positive range, decide_eq_true_eq]

end PDROC.D27Prepare.Search
