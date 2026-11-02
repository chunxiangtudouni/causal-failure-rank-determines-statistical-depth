module

public import PaperProofs.Paid.PDMenu_EndpointMinimum_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs

theorem paidEndpointObjective_toReal (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤) (m : ℕ) :
    (P.paidEndpointObjective fee hfee n k penalty m).toReal =
      (P.binarySymmetric.endpointCharge m : ℝ) +
      (1 - (P.binarySymmetric.endpointError m : ℝ)) * (P.paidGoodSuccessor fee hfee n k penalty).toReal +
      (P.binarySymmetric.endpointError m : ℝ) * (P.paidBadSuccessor fee hfee n k penalty).toReal := by
  have hgood := paidGoodSuccessor_ne_top P fee hfee n k penalty hp
  have hbad := paidBadSuccessor_ne_top P fee hfee n k penalty hp
  have he : 0 ≤ (P.binarySymmetric.endpointError m : ℝ) := by
    exact_mod_cast (P.binarySymmetric.endpointError_pos m).le
  have he1 : 0 ≤ 1 - (P.binarySymmetric.endpointError m : ℝ) := by
    have hhalf : (P.binarySymmetric.endpointError m : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr (P.binarySymmetric.endpointError_le_half m)
      norm_num at h
      exact h
    linarith
  have hc : 0 ≤ (P.binarySymmetric.endpointCharge m : ℝ) := by
    exact_mod_cast P.binarySymmetric.endpointCharge_nonneg m
  simp [Paid.Parameters.paidEndpointObjective, ENNReal.toReal_add,
    ENNReal.mul_ne_top, hgood, hbad, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    hc, he, he1]

theorem leastMinimizer_adjacent_strict (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (m : ℕ) (hm : 1 ≤ m)
    (hmin : P.IsLeastPaidEndpointMinimizer fee hfee n k penalty m) :
    P.paidEndpointObjective fee hfee n k penalty m < P.paidEndpointObjective fee hfee n k penalty (m - 1) := by
  apply lt_of_le_of_ne (hmin.1 (m - 1))
  intro heq
  have hother : P.IsPaidEndpointMinimizer fee hfee n k penalty (m - 1) := by
    intro index
    rw [← heq]
    exact hmin.1 index
  have := hmin.2 (m - 1) hother
  omega

theorem leastPositiveMinimizer_successors (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤)
    (m : ℕ) (hm : 1 ≤ m) (hmin : P.IsPaidEndpointMinimizer fee hfee n k penalty m) :
    P.paidGoodSuccessor fee hfee n k penalty ≤ P.paidBadSuccessor fee hfee n k penalty := by
  have hcomp := (ENNReal.toReal_le_toReal (paidEndpointObjective_ne_top P fee hfee n k penalty hp m)
    (paidEndpointObjective_ne_top P fee hfee n k penalty hp 0)).mpr (hmin 0)
  rw [paidEndpointObjective_toReal P fee hfee n k penalty hp m,
    paidEndpointObjective_toReal P fee hfee n k penalty hp 0] at hcomp
  have hc : 0 < (P.binarySymmetric.endpointCharge m : ℝ) := by
    have hl := endpointCharge_linear_lower P.binarySymmetric m
    have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    exact_mod_cast lt_of_lt_of_le (mul_pos P.binarySymmetric.reviewFee_pos hm0) hl
  have he : (P.binarySymmetric.endpointError m : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (P.binarySymmetric.endpointError_lt_half hm)
    norm_num at h
    exact h
  simp only [P.binarySymmetric.endpointCharge_zero, P.binarySymmetric.endpointError_zero,
    Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, zero_add] at hcomp
  apply (ENNReal.toReal_le_toReal (paidGoodSuccessor_ne_top P fee hfee n k penalty hp)
    (paidBadSuccessor_ne_top P fee hfee n k penalty hp)).mp
  by_contra h
  have hlt := lt_of_not_ge h
  nlinarith

theorem paidEndpoint_reduced_eq (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞)
    (horder : P.paidGoodSuccessor fee hfee n k penalty ≤ P.paidBadSuccessor fee hfee n k penalty) (m : ℕ) :
    P.paidEndpointObjective fee hfee n k penalty m =
      P.paidGoodSuccessor fee hfee n k penalty + P.paidReducedEndpointObjective fee hfee n k penalty m := by
  have he0 : 0 ≤ (P.binarySymmetric.endpointError m : ℝ) := by
    exact_mod_cast (P.binarySymmetric.endpointError_pos m).le
  have he1 : 0 ≤ 1 - (P.binarySymmetric.endpointError m : ℝ) := by
    have hh : (P.binarySymmetric.endpointError m : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr (P.binarySymmetric.endpointError_le_half m)
      norm_num at h
      exact h
    linarith
  have hweights : ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) +
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add he1 he0]
    norm_num
  have hbad : P.paidBadSuccessor fee hfee n k penalty = P.paidGoodSuccessor fee hfee n k penalty +
      P.paidSuccessorGap fee hfee n k penalty := by
    exact (add_tsub_cancel_of_le horder).symm
  unfold Paid.Parameters.paidEndpointObjective Paid.Parameters.paidReducedEndpointObjective
  rw [hbad]
  calc
    _ = (ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) +
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)) * P.paidGoodSuccessor fee hfee n k penalty +
      (ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) * P.paidSuccessorGap fee hfee n k penalty) := by ring
    _ = _ := by rw [hweights, one_mul]

theorem paidMenuNecessary (P : Paid.Parameters) : P.PaidMenuNecessary := by
  intro fee hfee n k penalty m _hn hp hm hmin
  have ho := leastPositiveMinimizer_successors P fee hfee n k penalty hp m hm hmin.1
  have hstrict := leastMinimizer_adjacent_strict P fee hfee n k penalty m hm hmin
  have hreal := (ENNReal.toReal_lt_toReal (paidEndpointObjective_ne_top P fee hfee n k penalty hp m)
    (paidEndpointObjective_ne_top P fee hfee n k penalty hp (m - 1))).mpr hstrict
  rw [paidEndpointObjective_toReal P fee hfee n k penalty hp m,
    paidEndpointObjective_toReal P fee hfee n k penalty hp (m - 1)] at hreal
  have hgap : (P.paidSuccessorGap fee hfee n k penalty).toReal =
      (P.paidBadSuccessor fee hfee n k penalty).toReal - (P.paidGoodSuccessor fee hfee n k penalty).toReal :=
    ENNReal.toReal_sub_of_le ho (paidBadSuccessor_ne_top P fee hfee n k penalty hp)
  have hc : (P.reviewFee : ℝ) ≤ (P.binarySymmetric.endpointCharge m : ℝ) -
      (P.binarySymmetric.endpointCharge (m - 1) : ℝ) := by
    exact_mod_cast (paidEndpointGrowth P).2 m hm
  have hem : 0 ≤ (P.binarySymmetric.endpointError m : ℝ) := by
    exact_mod_cast (P.binarySymmetric.endpointError_pos m).le
  have hg := ENNReal.toReal_nonneg (a := P.paidSuccessorGap fee hfee n k penalty)
  have hprod := mul_nonneg hg hem
  constructor
  · rw [paidEndpoint_reduced_eq P fee hfee n k penalty ho m,
      paidEndpoint_reduced_eq P fee hfee n k penalty ho (m - 1)] at hstrict
    exact lt_of_add_lt_add_left hstrict
  · apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top (paidBadSuccessor_ne_top P fee hfee n k penalty hp) tsub_le_self)
        ENNReal.ofReal_ne_top)).mp
    rw [ENNReal.toReal_ofReal (by exact_mod_cast P.reviewFee_pos.le), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by exact_mod_cast (P.binarySymmetric.endpointError_pos (m - 1)).le)]
    rw [hgap] at hprod
    rw [ENNReal.toReal_sub_of_le ho (paidBadSuccessor_ne_top P fee hfee n k penalty hp)]
    nlinarith

end PDMenu
