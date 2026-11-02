module

public import PaperProofs.Statistics.PDROC_Lower_001
public import PaperProofs.Paid.Claims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Statistics.BinarySymmetric

namespace PDROC

/-- The endpoint bias can at most double from any positive boundary to its successor.
This elementary rational proof suffices for the original four-factor charge bound. -/
theorem endpointBias_succ_le_two (P : Parameters) (m : ℕ) (hm : 1 ≤ m) :
    1 - 2 * P.endpointError (m + 1) ≤ 2 * (1 - 2 * P.endpointError m) := by
  have hr : 1 ≤ P.odds := P.odds_gt_one.le
  have hx : 1 ≤ P.odds ^ m := one_le_pow₀ hr
  have hpow : P.odds ^ (m + 1) ≤ (P.odds ^ m) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hr (by omega)
  have hy : 0 < 1 + P.odds ^ (m + 1) := by positivity
  have hxx : 0 < 1 + (P.odds ^ m) ^ 2 := by positivity
  have hmul : 1 / (1 + (P.odds ^ m) ^ 2) ≤ 1 / (1 + P.odds ^ (m + 1)) :=
    one_div_le_one_div_of_le hy (by linarith)
  have hid : 1 - 2 / (1 + (P.odds ^ m) ^ 2) ≤ 2 * (1 - 2 / (1 + P.odds ^ m)) := by
    field_simp
    nlinarith [sq_nonneg (P.odds ^ m - 1), mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (P.odds ^ m - 1))]
  unfold Parameters.endpointError
  simp only [div_eq_mul_inv] at hid hmul ⊢
  nlinarith

/-- Original D07 adjacent-charge ratio, proved in the exact rational formula. -/
theorem endpointCharge_succ_le_four (P : Parameters) (m : ℕ) (hm : 1 ≤ m) :
    P.endpointCharge (m + 1) ≤ 4 * P.endpointCharge m := by
  have hb := endpointBias_succ_le_two P m hm
  have hc : 0 ≤ P.reviewFee / (2 * P.gamma) := div_nonneg P.reviewFee_pos.le (by linarith [P.gamma_pos])
  have hn : (m + 1 : ℚ) ≤ 2 * (m : ℚ) := by exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hd : 0 ≤ 1 - 2 * P.endpointError m := by linarith [P.endpointError_le_half m]
  have h₁ := mul_le_mul_of_nonneg_left hb (show 0 ≤ (m + 1 : ℚ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * (1 - 2 * P.endpointError m) by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (h₁.trans h₂) hc
  rw [P.endpointCharge_formula, P.endpointCharge_formula]
  push_cast
  convert h₃ using 1 <;> ring

/-- Convexity places the information curve below every actual ROC chord. -/
theorem information_le_rocChord (P : Parameters) (m : ℕ) (p : ℝ)
    (hlower : (P.endpointError (m + 1) : ℝ) ≤ p)
    (hupper : p ≤ (P.endpointError m : ℝ)) :
    P.a * phiReal p ≤ P.rocChord m p := by
  have hmem (k : ℕ) : (P.endpointError k : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    constructor
    · exact_mod_cast P.endpointError_pos k
    · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half k)
      norm_num at hh
      exact hh
  have hw := P.rocWeight_mem_Icc m p hlower hupper
  have hi := P.rocWeight_error_interpolation m p
  have hconv := phiReal_convexOn.2 (hmem m) (hmem (m + 1)) hw.1
    (sub_nonneg.mpr hw.2) (by ring : P.rocWeight m p + (1 - P.rocWeight m p) = 1)
  simp only [smul_eq_mul] at hconv
  rw [hi] at hconv
  have hs := mul_le_mul_of_nonneg_left hconv P.a_pos.le
  rw [Parameters.rocChord, P.endpointCharge_eq_information, P.endpointCharge_eq_information]
  nlinarith only [hs]

/-- The first secant lies below every other chord, including beyond its own interval. -/
theorem firstChord_le_rocChord (P : Parameters) (m : ℕ) (p : ℝ)
    (hlower : (P.endpointError (m + 1) : ℝ) ≤ p)
    (hupper : p ≤ (P.endpointError m : ℝ)) :
    P.rocChord 0 p ≤ P.rocChord m p := by
  have hw := P.rocWeight_mem_Icc m p hlower hupper
  have h₁ := mul_le_mul_of_nonneg_left (rocChord_le_endpointCharge P 0 m) hw.1
  have h₂ := mul_le_mul_of_nonneg_left (rocChord_le_endpointCharge P 0 (m + 1))
    (sub_nonneg.mpr hw.2)
  have hi := P.rocWeight_error_interpolation m p
  have heq : P.rocWeight m p * P.rocChord 0 (P.endpointError m : ℝ) +
      (1 - P.rocWeight m p) * P.rocChord 0 (P.endpointError (m + 1) : ℝ) =
      P.rocChord 0 p := by
    conv_rhs => rw [← hi]
    unfold Parameters.rocChord Parameters.rocWeight
    ring
  rw [← heq]
  exact add_le_add h₁ h₂

theorem endpointError_one (P : Parameters) : P.endpointError 1 = 1 / 2 - P.gamma := by
  have hd : 1 - 2 * P.gamma ≠ 0 := ne_of_gt (by linarith [P.gamma_le_quarter])
  unfold Parameters.endpointError Parameters.odds
  rw [pow_one]
  field_simp
  ring

theorem endpointCharge_one (P : Parameters) : P.endpointCharge 1 = P.reviewFee := by
  rw [P.endpointCharge_formula, endpointError_one]
  field_simp [P.gamma_pos.ne']
  ring

/-- The exact first ROC chord is the linear part of the surrogate. -/
theorem firstChord_eq_linear (P : Parameters) (p : ℝ) :
    P.rocChord 0 p = (P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p) := by
  unfold Parameters.rocChord Parameters.rocWeight
  simp only [zero_add, P.endpointError_zero, P.endpointCharge_zero,
    endpointError_one, endpointCharge_one, Rat.cast_zero, Rat.cast_div,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, mul_zero, zero_add]
  have hg : (P.gamma : ℝ) ≠ 0 := by exact_mod_cast P.gamma_pos.ne'
  field_simp
  ring

theorem rocChord_le_endpointNext (P : Parameters) (m : ℕ) (p : ℝ)
    (hlower : (P.endpointError (m + 1) : ℝ) ≤ p)
    (hupper : p ≤ (P.endpointError m : ℝ)) :
    P.rocChord m p ≤ (P.endpointCharge (m + 1) : ℝ) := by
  have hw := P.rocWeight_mem_Icc m p hlower hupper
  have hc : (P.endpointCharge m : ℝ) ≤ (P.endpointCharge (m + 1) : ℝ) := by
    rw [P.endpointCharge_eq_information, P.endpointCharge_eq_information]
    apply mul_le_mul_of_nonneg_left _ P.a_pos.le
    apply phiReal_strictAntiOn.antitoneOn
    · constructor
      · exact_mod_cast P.endpointError_pos (m + 1)
      · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half (m + 1))
        norm_num at hh
        exact hh
    · constructor
      · exact_mod_cast P.endpointError_pos m
      · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half m)
        norm_num at hh
        exact hh
    · exact_mod_cast (P.endpointError_succ_lt m).le
  unfold Parameters.rocChord
  nlinarith only [mul_nonneg hw.1 (sub_nonneg.mpr hc)]

/-- Real scalar form of the two-sided uniformly attainable surrogate. -/
theorem rocChord_surrogate_bounds (P : Parameters) (p : ℝ) (hp : 0 < p)
    (hhalf : p ≤ 1 / 2) :
    max (P.a * phiReal p) ((P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p)) ≤
      P.rocChord (P.rocIndex p hp) p ∧
    P.rocChord (P.rocIndex p hp) p ≤
      4 * max (P.a * phiReal p) ((P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p)) := by
  let m := P.rocIndex p hp
  have hlo : (P.endpointError (m + 1) : ℝ) ≤ p := P.rocIndex_lower p hp
  have hhi : p ≤ (P.endpointError m : ℝ) := P.rocIndex_upper p hp hhalf
  constructor
  · exact max_le (information_le_rocChord P m p hlo hhi)
      (by rw [← firstChord_eq_linear]; exact firstChord_le_rocChord P m p hlo hhi)
  · by_cases hm : m = 0
    · change P.rocChord m p ≤ _
      rw [hm, firstChord_eq_linear]
      have hnn : 0 ≤ (P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p) := by
        apply mul_nonneg
        · exact div_nonneg (by exact_mod_cast P.reviewFee_pos.le) (by exact_mod_cast P.gamma_pos.le)
        · linarith
      have hmax := le_max_right (P.a * phiReal p) ((P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p))
      linarith
    · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hratio : (P.endpointCharge (m + 1) : ℝ) ≤ 4 * (P.endpointCharge m : ℝ) := by
        exact_mod_cast endpointCharge_succ_le_four P m hmpos
      have hinfo : (P.endpointCharge m : ℝ) ≤ P.a * phiReal p := by
        rw [P.endpointCharge_eq_information]
        apply mul_le_mul_of_nonneg_left _ P.a_pos.le
        apply phiReal_strictAntiOn.antitoneOn ⟨hp, hhalf⟩
        · constructor
          · exact_mod_cast P.endpointError_pos m
          · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half m)
            norm_num at hh
            exact hh
        · exact hhi
      have hbound := rocChord_le_endpointNext P m p hlo hhi
      have hmax := le_max_left (P.a * phiReal p) ((P.reviewFee : ℝ) / (P.gamma : ℝ) * (1 / 2 - p))
      change P.rocChord m p ≤ _
      linarith

/-- Original D07, with only the original paid parameter input. -/
theorem uniformLocalSurrogate (P : PaperProofs.Paid.Parameters) : P.UniformLocalSurrogate := by
  constructor
  · intro p hp hhalf
    have hb := rocChord_surrogate_bounds P.binarySymmetric p hp hhalf
    have he : P.rocSurrogate p = ENNReal.ofReal
        (max (P.binarySymmetric.a * phiReal p)
          ((P.binarySymmetric.reviewFee : ℝ) / (P.binarySymmetric.gamma : ℝ) * (1 / 2 - p))) := by
      rw [PaperProofs.Paid.Parameters.rocSurrogate, phi_of_pos hp,
        ← ENNReal.ofReal_mul P.a_pos.le,
        ← ENNReal.ofReal_mul (show 0 ≤ (P.reviewFee : ℝ) / (P.certificate.gamma : ℝ) by
          exact div_nonneg (by exact_mod_cast P.reviewFee_pos.le)
            (by exact_mod_cast P.certificate.gamma_pos.le)), ENNReal.ofReal_max]
      rfl
    rw [he, P.binarySymmetric.rocPrice_of_pos p hp hhalf]
    constructor
    · exact ENNReal.ofReal_le_ofReal hb.1
    · have h := ENNReal.ofReal_le_ofReal hb.2
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat] using h
  · exact endpointCharge_succ_le_four P.binarySymmetric

end PDROC
