module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
Real risk targets and rational executable targets, for the dyadic certificate
in `price-proofs.tex:263-275`. Reducing a risk target arbitrarily can increase
the original quota. The construction below stays in the same admissible dyadic
bin, including its rational lower endpoint, and preserves the minimal exponent.
It changes neither the original real-risk domain nor any native resource cap.
-/

@[expose] public section

namespace PaperProofs.Statistics

/-- Qualification in the paper's integer-power test; `C = 2 N C_N` there. -/
def DyadicQualifies (C : ℚ) (risk : ℝ) (exponent : ℕ) : Prop :=
  (C : ℝ) ≤ (2 : ℝ) ^ exponent * risk

/-- The paper minimizes over integer exponents at least one. -/
def IsMinimalDyadicExponent (C : ℚ) (risk : ℝ) (exponent : ℕ) : Prop :=
  1 ≤ exponent ∧ DyadicQualifies C risk exponent ∧
    ∀ smaller : ℕ, 1 ≤ smaller → smaller < exponent →
      ¬ DyadicQualifies C risk smaller

theorem dyadicQualifies_mono (C : ℚ) {risk risk' : ℝ} (exponent : ℕ)
    (h : risk ≤ risk') (hq : DyadicQualifies C risk exponent) :
    DyadicQualifies C risk' exponent := by
  exact hq.trans (mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num) exponent))

/-- A qualified real target admits a positive rational target within a factor two,
without losing qualification at the very same exponent. At the lower endpoint
the target itself is rational; strictly above it rational density applies. -/
theorem exists_rationalRisk_same_exponent (C : ℚ) (hC : 0 < C)
    (risk : ℝ) (hrisk : 0 < risk) (exponent : ℕ)
    (hq : DyadicQualifies C risk exponent) :
    ∃ r : ℚ, 0 < r ∧ risk / 2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ risk ∧
      DyadicQualifies C (r : ℝ) exponent := by
  let endpoint : ℚ := C / (2 : ℚ) ^ exponent
  have hpow : 0 < (2 : ℝ) ^ exponent := pow_pos (by norm_num) exponent
  have hendpoint_cast : (endpoint : ℝ) = (C : ℝ) / (2 : ℝ) ^ exponent := by
    simp [endpoint]
  have hendpoint_pos : 0 < endpoint :=
    div_pos hC (pow_pos (by norm_num) exponent)
  have hendpoint_le : (endpoint : ℝ) ≤ risk := by
    rw [hendpoint_cast]
    exact (div_le_iff₀ hpow).mpr (by simpa [DyadicQualifies, mul_comm] using hq)
  by_cases hboundary : (endpoint : ℝ) = risk
  · refine ⟨endpoint, hendpoint_pos, ?_, hboundary.le, ?_⟩
    · rw [hboundary]
      linarith
    · simpa only [hboundary] using hq
  · have hendpoint_lt : (endpoint : ℝ) < risk :=
      lt_of_le_of_ne hendpoint_le hboundary
    have hhalf : risk / 2 < risk := by linarith
    have hmax : max (risk / 2) (endpoint : ℝ) < risk :=
      max_lt_iff.mpr ⟨hhalf, hendpoint_lt⟩
    obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hmax
    have hhalf_r : risk / 2 < (r : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hrlo
    have hendpoint_r : (endpoint : ℝ) < (r : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hrlo
    have hrpos_real : 0 < (r : ℝ) := lt_trans (by linarith) hhalf_r
    have hrpos : 0 < r := by exact_mod_cast hrpos_real
    refine ⟨r, hrpos, hhalf_r.le, hrhi.le, ?_⟩
    have hdiv : (C : ℝ) / (2 : ℝ) ^ exponent ≤ (r : ℝ) := by
      rw [← hendpoint_cast]
      exact hendpoint_r.le
    have hmul := (div_le_iff₀ hpow).mp hdiv
    simpa [DyadicQualifies, mul_comm] using hmul

/-- Moving down in risk cannot make a previously unqualified smaller exponent qualify. -/
theorem minimalDyadicExponent_preserved (C : ℚ) {risk risk' : ℝ} (exponent : ℕ)
    (hminimal : IsMinimalDyadicExponent C risk exponent) (hle : risk' ≤ risk)
    (hq : DyadicQualifies C risk' exponent) :
    IsMinimalDyadicExponent C risk' exponent := by
  refine ⟨hminimal.1, hq, ?_⟩
  intro smaller hpos hsmall hqual
  exact hminimal.2.2 smaller hpos hsmall (dyadicQualifies_mono C smaller hle hqual)

/-- The original integer exponent, hence every rational quota depending only on that
exponent and fixed channel data, can be reused unchanged for the rational controller. -/
theorem exists_rationalRisk_preserves_minimal_exponent (C : ℚ) (hC : 0 < C)
    (risk : ℝ) (hrisk : 0 < risk) (exponent : ℕ)
    (hminimal : IsMinimalDyadicExponent C risk exponent) :
    ∃ r : ℚ, 0 < r ∧ risk / 2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ risk ∧
      IsMinimalDyadicExponent C (r : ℝ) exponent := by
  obtain ⟨r, hrpos, hhalf, hrle, hqual⟩ :=
    exists_rationalRisk_same_exponent C hC risk hrisk exponent hminimal.2.1
  exact ⟨r, hrpos, hhalf, hrle,
    minimalDyadicExponent_preserved C exponent hminimal hrle hqual⟩

/-- Local testing needs no native dyadic certificate, but uses the same conservative
rationalization of a positive real target. -/
theorem exists_rationalRisk_factorTwo (risk : ℝ) (hrisk : 0 < risk) :
    ∃ p : ℚ, 0 < p ∧ risk / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ risk := by
  have hhalf : risk / 2 < risk := by linarith
  obtain ⟨p, hp_lo, hp_hi⟩ := exists_rat_btwn hhalf
  have hp_real : 0 < (p : ℝ) := lt_trans (by linarith) hp_lo
  have hp : 0 < p := by exact_mod_cast hp_real
  exact ⟨p, hp, hp_lo.le, hp_hi.le⟩

/-- For a real penalty `t ≥ 4`, use a rational posterior target close to `1/t`.
This closes the rational-SPRT/real-penalty interface without pretending `1/t`
is rational. It keeps the penalty contribution at most one and changes the
logarithmic threshold by at most the fixed constant `log 2`. -/
theorem exists_rationalLocalPenaltyTarget (penalty : ℝ) (hpenalty : 4 ≤ penalty) :
    ∃ p : ℚ, 0 < p ∧ p ≤ 1 / 4 ∧
      (1 / penalty) / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 1 / penalty ∧
      penalty * (p : ℝ) ≤ 1 ∧
      Real.log penalty ≤ Real.log (1 / (p : ℝ)) ∧
      Real.log (1 / (p : ℝ)) ≤ Real.log penalty + Real.log 2 := by
  have ht : 0 < penalty := by linarith
  obtain ⟨p, hp, hp_lo, hp_hi⟩ :=
    exists_rationalRisk_factorTwo (1 / penalty) (one_div_pos.mpr ht)
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hp_quarter_real : (p : ℝ) ≤ (1 : ℝ) / 4 :=
    hp_hi.trans (one_div_le_one_div_of_le (by norm_num) hpenalty)
  have hp_quarter : p ≤ 1 / 4 := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using hp_quarter_real
  have hbudget : penalty * (p : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hp_hi ht.le
    simpa [ne_of_gt ht] using h
  have hinv_lo : penalty ≤ 1 / (p : ℝ) := (le_div_iff₀ hpr).mpr hbudget
  have hinv_hi : 1 / (p : ℝ) ≤ 2 * penalty := by
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp_lo
    have hmul := mul_le_mul_of_nonneg_left h ht.le
    apply (div_le_iff₀ hpr).mpr
    simpa [ne_of_gt ht, mul_assoc, mul_comm, mul_left_comm] using hmul
  refine ⟨p, hp, hp_quarter, hp_lo, hp_hi, hbudget,
    Real.log_le_log ht hinv_lo, ?_⟩
  have hlog := Real.log_le_log (one_div_pos.mpr hpr) hinv_hi
  simpa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht), add_comm] using hlog

/-- The paper's iterated logarithms: depth zero is the identity and depth one is log.
All statistical depth laws use fixed positive depth and sufficiently small risk. -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0, z => z
  | depth + 1, z => Real.log (iteratedLog depth z)

/-- Asymptotic interface proved in IteratedLog: a rational target chosen within a factor two of each
positive real target preserves every fixed positive iterated-log leading term.
This is separate from preservation of the native exponent. -/
def FactorTwoRiskIteratedLogStability : Prop :=
  ∀ depth : ℕ, 1 ≤ depth → ∀ choose : ℝ → ℚ,
    (∀ risk : ℝ, 0 < risk →
      risk / 2 ≤ (choose risk : ℝ) ∧ (choose risk : ℝ) ≤ risk) →
    Filter.Tendsto
      (fun risk : ℝ =>
        iteratedLog depth (1 / (choose risk : ℝ)) / iteratedLog depth (1 / risk))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

end PaperProofs.Statistics
