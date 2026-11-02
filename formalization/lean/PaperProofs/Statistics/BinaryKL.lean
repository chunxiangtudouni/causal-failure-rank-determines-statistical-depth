module

public import PaperProofs.Statistics.ChannelKL
public import PaperProofs.Statistics.DecisionLaw
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics

/-- Extended negative logarithm of a probability mass. In particular, zero
mass has value infinity, rather than the junk real value `Real.log 0`. -/
noncomputable def negativeLogMass (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 then ⊤ else ENNReal.ofReal (-Real.log p.toReal)

@[simp] theorem negativeLogMass_zero : negativeLogMass 0 = ⊤ := by
  simp [negativeLogMass]

@[simp] theorem negativeLogMass_one : negativeLogMass 1 = 0 := by
  simp [negativeLogMass]

theorem bool_singleton_compl (b : Bool) : ({b} : Set Bool)ᶜ = {!b} := by
  cases b <;> ext x <;> cases x <;> simp

theorem bool_mass_add_compl (μ : Measure Bool) [IsProbabilityMeasure μ] (b : Bool) :
    μ {b} + μ {!b} = 1 := by
  simpa only [bool_singleton_compl, measure_univ] using
    (measure_add_measure_compl (μ := μ) (measurableSet_singleton b))

theorem bool_real_mass_compl (μ : Measure Bool) [IsProbabilityMeasure μ] (b : Bool) :
    μ.real {!b} = 1 - μ.real {b} := by
  simpa only [bool_singleton_compl, measureReal_def, measure_univ,
    ENNReal.toReal_one] using
    (measureReal_compl (μ := μ) (measurableSet_singleton b))

theorem bool_rnDeriv_at (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (b : Bool) (hb : ν {b} ≠ 0) :
    μ.rnDeriv ν b = μ {b} / ν {b} := by
  have h := Measure.setLIntegral_rnDeriv hac ({b} : Set Bool)
  rw [lintegral_singleton] at h
  apply (ENNReal.eq_div_iff hb (measure_ne_top ν {b})).mpr
  simpa only [mul_comm] using h

theorem bool_integral_llr (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (b : Bool)
    (hb : ν {b} ≠ 0) (hnb : ν {!b} ≠ 0) :
    ∫ x, llr μ ν x ∂μ =
      μ.real {b} * Real.log (μ.real {b} / ν.real {b}) +
        μ.real {!b} * Real.log (μ.real {!b} / ν.real {!b}) := by
  have hpoint (x : Bool) (hx : ν {x} ≠ 0) :
      llr μ ν x = Real.log (μ.real {x} / ν.real {x}) := by
    rw [llr, bool_rnDeriv_at μ ν hac x hx, ENNReal.toReal_div]
    rfl
  rw [integral_fintype Integrable.of_finite]
  cases b <;> simp_all [smul_eq_mul, add_comm]

theorem mul_log_div_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  · rw [Real.log_div hp.ne' hq.ne']
    ring

theorem binary_real_kl_lower {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) :
    p * (-Real.log q) ≤
      (p * Real.log (p / q) +
        (1 - p) * Real.log ((1 - p) / (1 - q))) + Real.log 2 := by
  rw [mul_log_div_of_nonneg hp hq,
    mul_log_div_of_nonneg (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)]
  have hent := Real.binEntropy_le_log_two (p := p)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_def] at hent
  have hnegative := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp1)
    (Real.log_nonpos (sub_nonneg.mpr hq1.le) (by linarith : 1 - q ≤ 1))
  nlinarith

/-- Binary data-processing's elementary lower bound, expressed in ENNReal.
It includes all endpoint masses: `0 * infinity = 0`, and a positive mass
against a zero mass forces the actual measure KL to infinity. -/
theorem binary_kl_lower (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (b : Bool) :
    μ {b} * negativeLogMass (ν {b}) ≤
      InformationTheory.klDiv μ ν + ENNReal.ofReal (Real.log 2) := by
  by_cases hac : μ ≪ ν
  · by_cases hb : ν {b} = 0
    · have hμ : μ {b} = 0 := hac hb
      simp [hμ]
    · by_cases hnb : ν {!b} = 0
      · have hv : ν {b} = 1 := by simpa only [hnb, add_zero] using bool_mass_add_compl ν b
        simp [hv]
      · have hp : 0 ≤ μ.real {b} := ENNReal.toReal_nonneg
        have hp1 : μ.real {b} ≤ 1 := by
          have hmass : μ {b} ≤ (1 : ℝ≥0∞) := by
            calc
              μ {b} ≤ μ Set.univ := measure_mono (Set.subset_univ {b})
              _ = 1 := measure_univ
          simpa only [measureReal_def, ENNReal.toReal_one] using
            (ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
              hmass)
        have hq : 0 < ν.real {b} := ENNReal.toReal_pos hb (measure_ne_top ν {b})
        have hqn : 0 < ν.real {!b} := ENNReal.toReal_pos hnb (measure_ne_top ν {!b})
        have hq1 : ν.real {b} < 1 := by rw [bool_real_mass_compl ν b] at hqn; linarith
        have hbound := binary_real_kl_lower hp hp1 hq hq1
        rw [← bool_real_mass_compl μ b, ← bool_real_mass_compl ν b] at hbound
        rw [InformationTheory.klDiv_of_ac_of_integrable hac Integrable.of_finite]
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
        rw [bool_integral_llr μ ν hac b hb hnb]
        rw [negativeLogMass, ite_eq_right hb, ← ENNReal.ofReal_toReal (measure_ne_top μ {b}),
          ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        exact (ENNReal.ofReal_le_ofReal hbound).trans ENNReal.ofReal_add_le
  · simp [InformationTheory.klDiv_of_not_ac hac]

theorem bool_kl_eq_top_of_positive_zero (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (b : Bool)
    (hμ : 0 < μ {b}) (hν : ν {b} = 0) : InformationTheory.klDiv μ ν = ⊤ := by
  apply InformationTheory.klDiv_of_not_ac
  intro hac
  exact hμ.ne' (hac hν)

theorem binary_kl_lower_real (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (b : Bool) (hν : ν {b} ≠ 0)
    (hfinite : InformationTheory.klDiv μ ν ≠ ⊤) :
    μ.real {b} * Real.log ((ν.real {b})⁻¹) - Real.log 2 ≤
      (InformationTheory.klDiv μ ν).toReal := by
  have hq1 : ν.real {b} ≤ 1 := by
    have hmass : ν {b} ≤ (1 : ℝ≥0∞) := by
      calc
        ν {b} ≤ ν Set.univ := measure_mono (Set.subset_univ {b})
        _ = 1 := measure_univ
    simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hmass
  have hlog : 0 ≤ -Real.log (ν.real {b}) :=
    neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg hq1)
  change 0 ≤ -Real.log (ν {b}).toReal at hlog
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite, ENNReal.ofReal_ne_top⟩) (binary_kl_lower μ ν b)
  rw [ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top] at h
  simp only [negativeLogMass, ite_eq_right hν, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hlog, ENNReal.toReal_ofReal hlog2] at h
  rw [Real.log_inv]
  exact (sub_le_iff_le_add).mpr h

namespace BinaryExperiment

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The manuscript's `kl(1-alpha,beta)` bound for the actual, possibly
non-MAP decision. No stopped-information identity is used here. -/
theorem decisionLaw_kl_lower (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    (1 - E.conditionalError ν test x) * negativeLogMass (E.conditionalError ν test (!x)) ≤
      InformationTheory.klDiv (E.decisionLaw ν test x) (E.decisionLaw ν test (!x)) +
        ENNReal.ofReal (Real.log 2) := by
  have h := binary_kl_lower (E.decisionLaw ν test x) (E.decisionLaw ν test (!x)) x
  rw [E.decisionLaw_correct] at h
  have hother : E.decisionLaw ν test (!x) {x} = E.conditionalError ν test (!x) := by
    simpa only [Bool.not_not] using E.decisionLaw_error ν test (!x)
  rwa [hother] at h

end BinaryExperiment

end PaperProofs.Statistics
