module

public import PaperProofs.Paid.PDMenu_AdjacentNecessary_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs

theorem twoReviewFee_lt_Lambda (P : Paid.Parameters) : 2 * P.reviewFee < P.Lambda := by
  have hN : (1 : ℚ) ≤ P.certificate.stages := by exact_mod_cast P.certificate.stages_pos
  have ht : (1 : ℚ) ≤ P.certificate.t0 := by exact_mod_cast P.certificate.t0_pos
  have hNt : (1 : ℚ) ≤ (P.certificate.stages : ℚ) * P.certificate.t0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr ht)]
  have hB : P.reviewFee ≤ P.B := by
    unfold Paid.Parameters.B
    nlinarith [mul_nonneg P.reviewFee_pos.le (sub_nonneg.mpr hNt)]
  unfold Paid.Parameters.Lambda
  apply (lt_div_iff₀ P.certificate.risk_pos).mpr
  nlinarith [P.certificate.risk_le, P.reviewFee_pos,
    mul_nonneg P.reviewFee_pos.le (sub_nonneg.mpr P.certificate.risk_le)]

theorem menuEndpoint_pos (P : Paid.Parameters) : 1 ≤ P.certificate.M := by
  have hratio : P.reviewFee / P.Lambda < 1 / 2 := by
    apply (div_lt_iff₀ P.Lambda_pos).mpr
    linarith [twoReviewFee_lt_Lambda P]
  by_contra h
  have hM : P.certificate.M = 0 := by omega
  have hs := P.M_original_spec
  rw [hM] at hs
  norm_num [Paid.CertificateInput.rocError] at hs
  linarith

theorem odds_le_three (P : Statistics.BinarySymmetric.Parameters) : P.odds ≤ 3 := by
  unfold Statistics.BinarySymmetric.Parameters.odds
  apply (div_le_iff₀ (by linarith [P.gamma_le_quarter] : 0 < 1 - 2 * P.gamma)).mpr
  linarith [P.gamma_le_quarter]

theorem endpointError_div_odds_le_succ (P : Statistics.BinarySymmetric.Parameters) (m : ℕ) :
    P.endpointError m / P.odds ≤ P.endpointError (m + 1) := by
  have ha : 0 < P.odds := zero_lt_one.trans P.odds_gt_one
  unfold Statistics.BinarySymmetric.Parameters.endpointError
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity : 0 < 1 + P.odds ^ (m + 1))
  rw [pow_succ]
  nlinarith [P.odds_gt_one]

theorem menuEpsilon_floor (P : Paid.Parameters) :
    P.certificate.epsilon < P.binarySymmetric.endpointError (P.certificate.M - 1) / P.binarySymmetric.odds := by
  have hM := menuEndpoint_pos P
  have hnot := Nat.find_min P.certificate.exists_menuEndpoint (by omega : P.certificate.M - 1 < P.certificate.M)
  change ¬ P.certificate.rocError (P.certificate.M - 1) ≤ P.certificate.menuRatio at hnot
  have hprev : P.reviewFee / P.Lambda < P.binarySymmetric.endpointError (P.certificate.M - 1) := by
    rw [P.priceRatio_eq]
    exact lt_of_not_ge hnot
  have hr := P.epsilon_formula
  have heps : 3 * P.certificate.epsilon = P.reviewFee / P.Lambda := by rw [hr]; ring
  apply (lt_div_iff₀ (zero_lt_one.trans P.binarySymmetric.odds_gt_one)).mpr
  have hmul := mul_le_mul_of_nonneg_left (odds_le_three P.binarySymmetric) P.certificate.epsilon_pos.le
  nlinarith

theorem leastMinimizer_le_menuEndpoint (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ)
    (hn : 0 < n) (hp : penalty ≤ ENNReal.ofReal (P.Lambda : ℝ))
    (hmin : P.IsLeastPaidEndpointMinimizer fee hfee n k penalty m) : m ≤ P.certificate.M := by
  by_contra h
  have hm : P.certificate.M < m := lt_of_not_ge h
  have hpfin : penalty ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp
  have hnecessary := (paidMenuNecessary P fee hfee n k penalty m hn hpfin (by omega) hmin).2
  have hgap : P.paidSuccessorGap fee hfee n k penalty ≤ ENNReal.ofReal (P.Lambda : ℝ) :=
    tsub_le_self.trans ((paidBadSuccessor_le_penalty P fee hfee n k penalty).trans hp)
  have herror : P.binarySymmetric.endpointError (m - 1) ≤ P.reviewFee / P.Lambda := by
    exact (P.binarySymmetric.endpointError_strictAnti.antitone (by omega : P.certificate.M ≤ m - 1)).trans
      P.M_original_spec
  have hprod : P.paidSuccessorGap fee hfee n k penalty *
      ENNReal.ofReal (P.binarySymmetric.endpointError (m - 1) : ℝ) ≤ ENNReal.ofReal (P.reviewFee : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (P.Lambda : ℝ) * ENNReal.ofReal ((P.reviewFee / P.Lambda : ℚ) : ℝ) :=
        mul_le_mul' hgap (ENNReal.ofReal_le_ofReal (by exact_mod_cast herror))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by exact_mod_cast P.Lambda_pos.le)]
        congr 1
        push_cast
        field_simp [show (P.Lambda : ℝ) ≠ 0 by exact_mod_cast P.Lambda_pos.ne']
  exact (not_lt_of_ge hprod) hnecessary

theorem paidFiniteMenu (P : Paid.Parameters) : P.PaidFiniteMenu := by
  refine ⟨leastMinimizer_le_menuEndpoint P, twoReviewFee_lt_Lambda P,
    menuEndpoint_pos P, menuEpsilon_floor P, ?_⟩
  have hM := menuEndpoint_pos P
  have h := endpointError_div_odds_le_succ P.binarySymmetric (P.certificate.M - 1)
  simpa only [Nat.sub_add_cancel hM] using h

theorem paidPenaltyMenuClaims (P : Paid.Parameters) : P.PaidPenaltyMenuClaims :=
  ⟨paidEndpointGrowth P, paidEndpointMinimumExists P, paidMenuNecessary P, paidFiniteMenu P⟩

end PDMenu
