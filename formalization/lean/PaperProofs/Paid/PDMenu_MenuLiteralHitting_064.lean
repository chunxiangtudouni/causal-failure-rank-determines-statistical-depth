module

public import PaperProofs.Paid.PDLower_Majority_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open scoped BigOperators ENNReal

namespace PDMenu

open PaperProofs.Paid PaperProofs.Statistics

/-- The literal original native menu fold is the already-proved BSC walk,
without replacing it by a new test or an analysis-only prediction rule. -/
theorem menuScore_prefix_eq_signed (P : BinarySymmetric.Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val)) = P.signedSum tape n := by
  calc
    _ = ∑ i : Fin n, PDLower.majorityScoreStep (tape i.val).val :=
      PDLower.majorityWordScore_ofFn (fun i : Fin n => tape i.val)
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => PDLower.majorityScoreStep (tape i).val) n

theorem menuScore_logOdds (P : BinarySymmetric.Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    P.experiment.logOddsScore tape n =
      P.h * (Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val)) : ℝ) := by
  rw [P.logOddsScore_eq_signed, menuScore_prefix_eq_signed]

theorem menuScore_hitting_stop_le (P : BinarySymmetric.Parameters) (level : ℕ) (tape : P.experiment.Tape) (n : ℕ) :
    (P.symmetricHittingTest level).rule.stop () tape ≤ n ↔
      ∃ k ≤ n, level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin k => (tape i.val).val))).natAbs := by
  rw [P.symmetricHittingTest_stop_le_iff]
  simp_rw [menuScore_prefix_eq_signed]

theorem menuScore_hitting_stop_eq (P : BinarySymmetric.Parameters) (level : ℕ) (tape : P.experiment.Tape) (n : ℕ) :
    (P.symmetricHittingTest level).rule.stop () tape = n ↔
      level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val))).natAbs ∧
      ∀ k < n, (Parameters.menuWordScore (List.ofFn (fun i : Fin k => (tape i.val).val))).natAbs < level := by
  constructor
  · intro hstop
    have hle : (P.symmetricHittingTest level).rule.stop () tape ≤ n := hstop.le
    obtain ⟨k, hkn, hhit⟩ := (menuScore_hitting_stop_le P level tape n).mp hle
    have hsk := (menuScore_hitting_stop_le P level tape k).mpr ⟨k, le_rfl, hhit⟩
    rw [hstop] at hsk
    have hnk : n ≤ k := ENat.natCast_le_natCast.mp hsk
    have heq : k = n := le_antisymm hkn hnk
    subst k
    refine ⟨hhit, ?_⟩
    intro j hj
    by_contra hnot
    have hs := (menuScore_hitting_stop_le P level tape j).mpr ⟨j, le_rfl, Nat.le_of_not_gt hnot⟩
    rw [hstop] at hs
    exact (Nat.not_le_of_gt hj) (ENat.natCast_le_natCast.mp hs)
  · rintro ⟨hhit, hbefore⟩
    have hle := (menuScore_hitting_stop_le P level tape n).mpr ⟨n, le_rfl, hhit⟩
    apply le_antisymm hle
    cases n with
    | zero => exact zero_le
    | succ n =>
      apply ENat.natCast_add_one_le_iff.mpr
      apply lt_of_not_ge
      intro hs
      obtain ⟨j, hj, hhitj⟩ := (menuScore_hitting_stop_le P level tape n).mp hs
      exact (Nat.not_le_of_gt (hbefore j (Nat.lt_succ_of_le hj))) hhitj

theorem menuScore_hitting_decision (P : BinarySymmetric.Parameters) (level : ℕ) (tape : P.experiment.Tape) (n : ℕ)
    (hstop : (P.symmetricHittingTest level).rule.stop () tape = n) :
    (P.symmetricHittingTest level).rule.decision () tape =
      decide (0 ≤ Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val))) := by
  change P.experiment.posteriorThresholdStop (P.endpointError level) tape = n at hstop
  change decide (0 ≤ P.experiment.logOddsScore tape
    (P.experiment.posteriorThresholdStop (P.endpointError level) tape).toNat) = _
  rw [hstop, ENat.toNat_natCast, menuScore_logOdds]
  by_cases hnonneg : 0 ≤ Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val))
  · have hr : 0 ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val)) : ℝ) := by
      exact_mod_cast hnonneg
    simp only [hnonneg, mul_nonneg P.h_pos.le hr, decide_true]
  · have hr : (Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val)) : ℝ) < 0 := by
      exact_mod_cast lt_of_not_ge hnonneg
    have hn : ¬ 0 ≤ P.h * (Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val)) : ℝ) :=
      not_le.mpr (mul_neg_of_pos_of_neg P.h_pos hr)
    simp only [hnonneg, hn, decide_false]

end PDMenu
