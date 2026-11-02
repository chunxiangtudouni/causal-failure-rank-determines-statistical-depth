module

public import PaperProofs.Statistics.LocalUpper
public import PaperProofs.Statistics.StoppedWald
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory Filter

namespace PaperProofs.Statistics

theorem negativeLogMass_antitone : Antitone negativeLogMass := by
  intro p q hpq
  by_cases hq : q = ⊤
  · subst q
    simp [negativeLogMass]
  · by_cases hp0 : p = 0
    · simp [hp0]
    · have hq0 : q ≠ 0 := ne_bot_of_le_ne_bot hp0 hpq
      have hp : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
      have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
      have hpqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
      simp only [negativeLogMass, ite_eq_right hp0, ite_eq_right hq0]
      exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log hpr hpqr))

namespace BinaryExperiment

variable {Seed : Type} [MeasurableSpace Seed]

theorem decision_information_lower (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    E.decisionInformationDemand ν test x ≤
      ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x +
        ENNReal.ofReal (Real.log 2) :=
  E.decision_information_lower_of_finite E.stoppedInformationIdentity ν test hfinite x

theorem decision_information_lower_of_objective (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : E.bayesObjective ν test penalty ≠ ⊤) (x : Bool) :
    E.decisionInformationDemand ν test x ≤
      ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x +
        ENNReal.ofReal (Real.log 2) :=
  E.decision_information_lower_of_finite_objective
    E.stoppedInformationIdentity ν test penalty hfinite x

theorem bayesInformationLower_le_observationCharge_unconditional
    (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) :
    E.bayesInformationLower ν test ≤ E.bayesObservationCharge ν test :=
  E.bayesInformationLower_le_observationCharge E.stoppedInformationIdentity ν test

noncomputable def leastPrior (E : BinaryExperiment) : ℝ :=
  min (E.priorReal false) (E.priorReal true)

theorem leastPrior_pos (E : BinaryExperiment) : 0 < E.leastPrior :=
  lt_min (E.priorReal_pos false) (E.priorReal_pos true)

theorem leastPrior_le (E : BinaryExperiment) (x : Bool) : E.leastPrior ≤ E.priorReal x := by
  cases x
  · exact min_le_left _ _
  · exact min_le_right _ _

noncomputable def cheapErrorConstant (E : BinaryExperiment) : ℝ :=
  2 * E.coefficient / E.leastPrior

theorem cheapErrorConstant_pos (E : BinaryExperiment) : 0 < E.cheapErrorConstant :=
  div_pos (mul_pos (by norm_num) E.coefficient_pos) E.leastPrior_pos

noncomputable def cheapError (E : BinaryExperiment) (t : ℝ) : ℝ :=
  E.cheapErrorConstant * Real.log t / t

theorem conditionalError_real_le_of_objective_bound (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (t B : ℝ)
    (ht : 0 < t) (hB : 0 ≤ B)
    (hbound : E.bayesObjective ν test (ENNReal.ofReal t) ≤ ENNReal.ofReal B) (x : Bool) :
    (E.conditionalError ν test x).toReal ≤ B / (t * E.priorReal x) := by
  have hweighted : ENNReal.ofReal t * (E.priorMass x * E.conditionalError ν test x) ≤
      ENNReal.ofReal B := by
    have hsingle : E.priorMass x * E.conditionalError ν test x ≤ E.bayesError ν test := by
      unfold bayesError
      exact Finset.single_le_sum
        (f := fun y : Bool => E.priorMass y * E.conditionalError ν test y)
        (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ x)
    calc
      _ ≤ ENNReal.ofReal t * E.bayesError ν test := by
        exact mul_le_mul' le_rfl hsingle
      _ ≤ E.bayesObjective ν test (ENNReal.ofReal t) := le_add_self
      _ ≤ _ := hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweighted
  simp only [ENNReal.toReal_mul, priorMass, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (E.priorReal_pos x).le, ENNReal.toReal_ofReal hB] at hreal
  apply (le_div_iff₀ (mul_pos ht (E.priorReal_pos x))).mpr
  nlinarith

theorem conditionalError_le_cheapError (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (t : ℝ) (ht : 1 < t)
    (hbound : E.bayesObjective ν test (ENNReal.ofReal t) ≤
      ENNReal.ofReal (2 * E.coefficient * Real.log t)) (x : Bool) :
    E.conditionalError ν test x ≤ ENNReal.ofReal (E.cheapError t) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hB : 0 ≤ 2 * E.coefficient * Real.log t := by
    exact mul_nonneg (mul_nonneg (by norm_num) E.coefficient_pos.le) (Real.log_pos ht).le
  have hreal := E.conditionalError_real_le_of_objective_bound ν test t _ ht0 hB hbound x
  have hdenom : 0 < t * E.leastPrior := mul_pos ht0 E.leastPrior_pos
  have hdenomle : t * E.leastPrior ≤ t * E.priorReal x :=
    mul_le_mul_of_nonneg_left (E.leastPrior_le x) ht0.le
  have hcommon : (E.conditionalError ν test x).toReal ≤
      (2 * E.coefficient * Real.log t) / (t * E.leastPrior) :=
    hreal.trans (div_le_div_of_nonneg_left hB hdenom hdenomle)
  have heq : (2 * E.coefficient * Real.log t) / (t * E.leastPrior) = E.cheapError t := by
    unfold cheapError cheapErrorConstant
    ring
  rw [heq] at hcommon
  rw [← ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) (E.conditionalError_le_one ν test x))]
  exact ENNReal.ofReal_le_ofReal hcommon

theorem informationDemand_ge_uniform_error (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (herrors : ∀ x, E.conditionalError ν test x ≤ ENNReal.ofReal e) (x : Bool) :
    ENNReal.ofReal ((1 - e) * (-Real.log e)) ≤ E.decisionInformationDemand ν test x := by
  have hcorrect : ENNReal.ofReal (1 - e) ≤ 1 - E.conditionalError ν test x := by
    rw [ENNReal.ofReal_sub 1 he.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (herrors x) 1
  have hlog : ENNReal.ofReal (-Real.log e) ≤
      negativeLogMass (E.conditionalError ν test (!x)) := by
    have h := negativeLogMass_antitone (herrors (!x))
    simpa only [negativeLogMass, ite_eq_right (ne_of_gt (ENNReal.ofReal_pos.mpr he)),
      ENNReal.toReal_ofReal he.le] using h
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr he1)]
  exact mul_le_mul' hcorrect hlog

theorem observationCharge_ge_uniform_error (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (herrors : ∀ x, E.conditionalError ν test x ≤ ENNReal.ofReal e) :
    ENNReal.ofReal (E.coefficient * ((1 - e) * (-Real.log e) - Real.log 2)) ≤
      E.bayesObservationCharge ν test := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hpoint (x : Bool) : ENNReal.ofReal ((1 - e) * (-Real.log e) - Real.log 2) ≤
      E.decisionInformationDemand ν test x - ENNReal.ofReal (Real.log 2) := by
    rw [ENNReal.ofReal_sub _ hlog2]
    exact tsub_le_tsub_right (E.informationDemand_ge_uniform_error ν test e he he1 herrors x) _
  calc
    _ = (∑ x : Bool, E.informationWeight x) *
        ENNReal.ofReal ((1 - e) * (-Real.log e) - Real.log 2) := by
      rw [E.informationWeight_sum, ← ENNReal.ofReal_mul E.coefficient_pos.le]
    _ ≤ E.bayesInformationLower ν test := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul' le_rfl (hpoint x)
    _ ≤ _ := E.bayesInformationLower_le_observationCharge E.stoppedInformationIdentity ν test

noncomputable def localLowerCurve (E : BinaryExperiment) (t : ℝ) : ℝ :=
  min (2 * E.coefficient * Real.log t)
    (E.coefficient * ((1 - E.cheapError t) * (-Real.log (E.cheapError t)) - Real.log 2))

theorem cheapError_pos (E : BinaryExperiment) (t : ℝ) (ht : 1 < t) :
    0 < E.cheapError t :=
  div_pos (mul_pos E.cheapErrorConstant_pos (Real.log_pos ht)) (lt_trans zero_lt_one ht)

/-- Uniform lower bound on the actual policy infimum. Each original test is
either already expensive, or its own objective bounds both actual errors. -/
theorem localValue_lower_curve (E : BinaryExperiment) (t : ℝ) (ht : 1 < t)
    (he1 : E.cheapError t ≤ 1) :
    ENNReal.ofReal (E.localLowerCurve t) ≤ E.localValue (ENNReal.ofReal t) := by
  unfold localValue
  apply le_iInf
  intro TestSeed
  apply le_iInf
  intro m
  let : MeasurableSpace TestSeed := m
  apply le_iInf
  intro ν
  apply le_iInf
  intro hν
  have : IsProbabilityMeasure ν := hν
  apply le_iInf
  intro test
  by_cases hsmall : E.bayesObjective ν test (ENNReal.ofReal t) ≤
      ENNReal.ofReal (2 * E.coefficient * Real.log t)
  · have herrors := E.conditionalError_le_cheapError ν test t ht hsmall
    have hinfo := E.observationCharge_ge_uniform_error ν test
      (E.cheapError t) (E.cheapError_pos t ht) he1 herrors
    calc
      _ ≤ ENNReal.ofReal (E.coefficient *
          ((1 - E.cheapError t) * (-Real.log (E.cheapError t)) - Real.log 2)) :=
        ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ E.bayesObservationCharge ν test := hinfo
      _ ≤ _ := le_self_add
  · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (le_of_lt (lt_of_not_ge hsmall))

theorem cheapError_tendsto_zero (E : BinaryExperiment) :
    Tendsto E.cheapError atTop (nhds 0) := by
  change Tendsto (fun t : ℝ => E.cheapErrorConstant * Real.log t / t) atTop (nhds 0)
  have hbase : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => E.cheapErrorConstant)
    atTop (nhds E.cheapErrorConstant)).mul hbase
  simpa only [mul_zero, mul_div_assoc] using h

theorem cheapError_log_ratio_tendsto_one (E : BinaryExperiment) :
    Tendsto (fun t : ℝ => -Real.log (E.cheapError t) / Real.log t) atTop (nhds 1) := by
  have hbase : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t) / Real.log t)
      atTop (nhds 0) := hbase.comp Real.tendsto_log_atTop
  have hconst : Tendsto (fun t : ℝ => Real.log E.cheapErrorConstant / Real.log t)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto (fun t : ℝ =>
      1 - Real.log E.cheapErrorConstant / Real.log t -
        Real.log (Real.log t) / Real.log t) atTop (nhds 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hconst).sub hloglog
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  rw [cheapError, Real.log_div
    (mul_ne_zero E.cheapErrorConstant_pos.ne' hlog.ne') ht0.ne',
    Real.log_mul E.cheapErrorConstant_pos.ne' hlog.ne']
  field_simp
  ring

theorem uniformInformation_shape_tendsto_one (E : BinaryExperiment) :
    Tendsto (fun t : ℝ =>
      ((1 - E.cheapError t) * (-Real.log (E.cheapError t)) - Real.log 2) / Real.log t)
      atTop (nhds 1) := by
  have hconst : Tendsto (fun t : ℝ => Real.log 2 / Real.log t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := ((hone.sub E.cheapError_tendsto_zero).mul
    E.cheapError_log_ratio_tendsto_one).sub hconst
  simpa only [sub_zero, one_mul, sub_div, mul_div_assoc] using h

/-- The lower half is unconditional: the stopped-information identity has
already been proved, and the infimum still ranges over all original rules. -/
theorem localValue_ratio_eventually_ge (E : BinaryExperiment) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      1 - ε ≤ E.localValueReal t / (E.coefficient * Real.log t) := by
  have he1 : ∀ᶠ t : ℝ in atTop, E.cheapError t < 1 :=
    E.cheapError_tendsto_zero.eventually (gt_mem_nhds zero_lt_one)
  have hshape : ∀ᶠ t : ℝ in atTop, 1 - ε <
      ((1 - E.cheapError t) * (-Real.log (E.cheapError t)) - Real.log 2) / Real.log t :=
    E.uniformInformation_shape_tendsto_one.eventually (lt_mem_nhds (by linarith))
  filter_upwards [eventually_gt_atTop (1 : ℝ), he1, hshape] with t ht he1 hshape
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hdenom : 0 < E.coefficient * Real.log t := mul_pos E.coefficient_pos hlog
  have hfirst : (1 - ε) * (E.coefficient * Real.log t) ≤
      2 * E.coefficient * Real.log t := by
    have h := mul_le_mul_of_nonneg_right (show 1 - ε ≤ 2 by linarith) hdenom.le
    simpa only [mul_assoc] using h
  have hsecond : (1 - ε) * (E.coefficient * Real.log t) ≤ E.coefficient *
      ((1 - E.cheapError t) * (-Real.log (E.cheapError t)) - Real.log 2) := by
    have h := mul_le_mul_of_nonneg_left ((lt_div_iff₀ hlog).mp hshape).le E.coefficient_pos.le
    convert h using 1
    ring
  have hcurve : (1 - ε) * (E.coefficient * Real.log t) ≤ E.localLowerCurve t :=
    le_min hfirst hsecond
  have hENN := (ENNReal.ofReal_le_ofReal hcurve).trans (E.localValue_lower_curve t ht he1.le)
  have hreal : (1 - ε) * (E.coefficient * Real.log t) ≤ E.localValueReal t :=
    (ENNReal.ofReal_le_iff_le_toReal (E.localValue_ofReal_ne_top t)).mp hENN
  exact (le_div_iff₀ hdenom).mpr hreal

theorem localLogarithmicPrice_of_sprt (E : BinaryExperiment)
    (hsprt : E.PosteriorSPRTGuarantee) : E.LocalLogarithmicPrice := by
  unfold LocalLogarithmicPrice
  apply tendsto_order.2
  constructor
  · intro a ha
    have h := E.localValue_ratio_eventually_ge ((1 - a) / 2) (by linarith)
    filter_upwards [h] with t ht
    linarith
  · intro b hb
    have h := E.localValue_ratio_eventually_le_of_sprt hsprt ((b - 1) / 2) (by linarith)
    filter_upwards [h] with t ht
    linarith

end BinaryExperiment
end PaperProofs.Statistics
