module

public import PaperProofs.Statistics.LocalInformation
public import PaperProofs.Statistics.RationalRisk
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory Filter

namespace PaperProofs.Statistics.BinaryExperiment

variable {Seed : Type} [MeasurableSpace Seed]

theorem bayesObservationCharge_le_drift_bound (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (B : ℝ) (hB : 0 ≤ B)
    (hfinite : ∀ x, E.expectedObservationCharge ν test x ≠ ⊤)
    (hbound : ∀ x, (E.expectedObservationCharge ν test x).toReal ≤
      (E.observationFee : ℝ) / E.divergence x * B) :
    E.bayesObservationCharge ν test ≤ ENNReal.ofReal (E.coefficient * B) := by
  have hnonneg (x : Bool) :
      0 ≤ E.priorReal x * ((E.observationFee : ℝ) / E.divergence x * B) :=
    mul_nonneg (E.priorReal_pos x).le
      (mul_nonneg (div_nonneg E.observationFee_real_pos.le (E.divergence_pos x).le) hB)
  calc
    _ ≤ ∑ x : Bool, ENNReal.ofReal
        (E.priorReal x * ((E.observationFee : ℝ) / E.divergence x * B)) := by
      unfold bayesObservationCharge
      apply Finset.sum_le_sum
      intro x _
      have hc : E.expectedObservationCharge ν test x ≤
          ENNReal.ofReal ((E.observationFee : ℝ) / E.divergence x * B) := by
        rw [← ENNReal.ofReal_toReal (hfinite x)]
        exact ENNReal.ofReal_le_ofReal (hbound x)
      calc
        _ ≤ E.priorMass x *
            ENNReal.ofReal ((E.observationFee : ℝ) / E.divergence x * B) :=
          mul_le_mul' le_rfl hc
        _ = _ := by rw [priorMass, ← ENNReal.ofReal_mul (E.priorReal_pos x).le]
    _ = ENNReal.ofReal (E.coefficient * B) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hnonneg x)]
      congr 1
      rw [coefficient, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- The actual rational posterior-SPRT guarantee suffices for the sharp
numeric upper bound. No asymptotic target is assumed. -/
theorem localValue_log_upper_of_sprt (E : BinaryExperiment)
    (hsprt : E.PosteriorSPRTGuarantee) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 4 ≤ t →
      E.localValueReal t ≤ E.coefficient * Real.log t + C := by
  obtain ⟨K, hK, htests⟩ := hsprt
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  let C := E.coefficient * (K + Real.log 2) + 1
  have hC : 0 ≤ C :=
    add_nonneg (mul_nonneg E.coefficient_pos.le (add_nonneg hK hlog2)) zero_le_one
  refine ⟨C, hC, ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  obtain ⟨p, hp, hpquarter, _, _, htp, _, hlogp⟩ :=
    exists_rationalLocalPenaltyTarget t ht
  obtain ⟨test, _, herr, hconditional⟩ := htests p hp hpquarter
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpReal1 : (p : ℝ) ≤ 1 := by exact_mod_cast hpquarter.trans (by norm_num : (1 : ℚ) / 4 ≤ 1)
  have hB : 0 ≤ Real.log (1 / (p : ℝ)) + K := by
    have hone : 1 ≤ 1 / (p : ℝ) := (le_div_iff₀ hpReal).mpr (by simpa using hpReal1)
    exact add_nonneg (Real.log_nonneg hone) hK
  have hobs := E.bayesObservationCharge_le_drift_bound (Measure.dirac ()) test
    (Real.log (1 / (p : ℝ)) + K) hB
    (fun x => (hconditional x).2.1) (fun x => (hconditional x).2.2)
  have hpenalty : ENNReal.ofReal t * E.bayesError (Measure.dirac ()) test ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal t * ENNReal.ofReal (p : ℝ) := mul_le_mul' le_rfl herr
      _ = ENNReal.ofReal (t * (p : ℝ)) := (ENNReal.ofReal_mul htpos.le).symm
      _ ≤ 1 := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal htp
  have hJ : E.localValue (ENNReal.ofReal t) ≤
      ENNReal.ofReal (E.coefficient * Real.log t + C) := by
    calc
      _ ≤ E.bayesObjective (Measure.dirac ()) test (ENNReal.ofReal t) :=
        E.localValue_le_test (Measure.dirac ()) test _
      _ ≤ ENNReal.ofReal (E.coefficient * (Real.log (1 / (p : ℝ)) + K)) + 1 :=
        add_le_add hobs hpenalty
      _ = ENNReal.ofReal (E.coefficient * (Real.log (1 / (p : ℝ)) + K) + 1) := by
        rw [ENNReal.ofReal_add (mul_nonneg E.coefficient_pos.le hB) (by norm_num)]
        simp only [ENNReal.ofReal_one]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left hlogp E.coefficient_pos.le]
  have hnonneg : 0 ≤ E.coefficient * Real.log t + C :=
    add_nonneg (mul_nonneg E.coefficient_pos.le (Real.log_nonneg (by linarith))) hC
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJ
  simpa only [localValueReal, ENNReal.toReal_ofReal hnonneg] using hreal

theorem small_penalty_le_log (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    t ≤ 3 * Real.log (1 + t) := by
  have hlog := Real.le_log_one_add_of_nonneg ht
  have hnonneg : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hdenom : 0 < t + 2 := by linarith
  have hmul := (div_le_iff₀ hdenom).mp hlog
  nlinarith [mul_nonneg hnonneg (show 0 ≤ 4 - t by linarith)]

theorem globalLogarithmicEnvelope_of_sprt (E : BinaryExperiment)
    (hsprt : E.PosteriorSPRTGuarantee) : E.GlobalLogarithmicEnvelope := by
  obtain ⟨C, hC, hlarge⟩ := E.localValue_log_upper_of_sprt hsprt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let K := 3 + E.coefficient + C / Real.log 2
  have hdiv : 0 ≤ C / Real.log 2 := div_nonneg hC hlog2.le
  have hK : 0 ≤ K := add_nonneg (add_nonneg (by norm_num) E.coefficient_pos.le) hdiv
  refine ⟨K, hK, ?_⟩
  intro t ht
  have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  by_cases ht4 : t ≤ 4
  · calc
      _ ≤ t := E.localValueReal_le t ht
      _ ≤ 3 * Real.log (1 + t) := small_penalty_le_log t ht ht4
      _ ≤ K * Real.log (1 + t) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        dsimp [K]
        linarith [E.coefficient_pos]
  · have htpos : 0 < t := by linarith
    have hlogt : Real.log t ≤ Real.log (1 + t) := Real.log_le_log htpos (by linarith)
    have hlog2le : Real.log 2 ≤ Real.log (1 + t) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hconstant : C ≤ C / Real.log 2 * Real.log (1 + t) := by
      calc
        C = C / Real.log 2 * Real.log 2 := (div_mul_cancel₀ C hlog2.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog2le hdiv
    calc
      _ ≤ E.coefficient * Real.log t + C := hlarge t (by linarith)
      _ ≤ E.coefficient * Real.log (1 + t) + C / Real.log 2 * Real.log (1 + t) :=
        add_le_add (mul_le_mul_of_nonneg_left hlogt E.coefficient_pos.le) hconstant
      _ ≤ K * Real.log (1 + t) := by dsimp [K]; nlinarith

/-- The upper half of the sharp logarithmic asymptotic, in an eventual
epsilon form that can be combined with an independently proved lower half. -/
theorem localValue_ratio_eventually_le_of_sprt (E : BinaryExperiment)
    (hsprt : E.PosteriorSPRTGuarantee) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      E.localValueReal t / (E.coefficient * Real.log t) ≤ 1 + ε := by
  obtain ⟨C, _, hlarge⟩ := E.localValue_log_upper_of_sprt hsprt
  have hlim : Tendsto (fun t : ℝ => C / (E.coefficient * Real.log t)) atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (nhds C)).div_atTop
      (Tendsto.const_mul_atTop E.coefficient_pos Real.tendsto_log_atTop)
  have hsmall : ∀ᶠ t : ℝ in atTop, C / (E.coefficient * Real.log t) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_gt_atTop (1 : ℝ), hsmall]
    with t ht ht1 hsmall
  have hdenom : 0 < E.coefficient * Real.log t :=
    mul_pos E.coefficient_pos (Real.log_pos ht1)
  have hratio : E.localValueReal t / (E.coefficient * Real.log t) ≤
      1 + C / (E.coefficient * Real.log t) := by
    apply (div_le_iff₀ hdenom).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ C hdenom.ne']
    exact hlarge t ht
  exact hratio.trans (by linarith)

end PaperProofs.Statistics.BinaryExperiment
