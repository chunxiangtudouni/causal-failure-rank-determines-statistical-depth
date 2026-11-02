module

public import PaperProofs.Statistics.SymmetricHitting

/-! Exact D04 laws for the already defined real symmetric hitting test.
Uses the actual stopped-transcript density and Wald, with no new test fields. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinarySymmetric.Parameters

theorem symmetricHitting_stoppedScore_abs_ae (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    ∀ᵐ record ∂(P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x),
      |P.experiment.stoppedWordScore record.2| = (m : ℝ) * P.h := by
  have hmeas : MeasurableSet {record : Unit × P.experiment.StoppedWord |
      |P.experiment.stoppedWordScore record.2| = (m : ℝ) * P.h} :=
    (P.experiment.measurable_stoppedWordScore.comp measurable_snd).norm (measurableSet_singleton _)
  apply (ae_map_iff (P.experiment.measurable_stoppedTranscript (P.symmetricHittingTest m)).aemeasurable hmeas).mpr
  filter_upwards [P.experiment.expectedSamples_finite_stop (Measure.dirac ()) (P.symmetricHittingTest m) x
    (P.symmetricHittingTest_expectedSamples_finite m x)] with sample hs
  rcases sample with ⟨⟨⟩, tape⟩
  have hhit := P.symmetricHittingTest_hits_exact m hm tape _ (ENat.natCast_toNat hs).symm
  change |P.experiment.stoppedWordScore
    (P.experiment.stoppedTranscript (P.experiment.posteriorSPRT (P.endpointError m)) ((), tape)).2| = _
  rw [P.experiment.stoppedWordScore_transcript, P.abs_logOddsScore_eq]
  change (P.signedSum tape (P.experiment.posteriorThresholdStop (P.endpointError m) tape).toNat).natAbs = m at hhit
  change P.h * ((P.signedSum tape (P.experiment.posteriorThresholdStop (P.endpointError m) tape).toNat).natAbs : ℝ) = _
  rw [hhit]
  ring

theorem stoppedWordScore_eq_wordLogLikelihood (P : Parameters) (word : P.experiment.StoppedWord) :
    P.experiment.stoppedWordScore word = P.experiment.wordLogLikelihood true word := by
  simp [BinaryExperiment.stoppedWordScore, BinaryExperiment.priorReal, P.prior_eq_half]

theorem exp_endpointThreshold (P : Parameters) (m : ℕ) :
    Real.exp ((m : ℝ) * P.h) = (P.odds : ℝ) ^ m := by
  rw [Real.exp_nat_mul]
  have ho : 0 < (P.odds : ℝ) := by exact_mod_cast (zero_lt_one.trans P.odds_gt_one)
  rw [h, Real.exp_log ho]

theorem symmetricHitting_transcriptLikelihood_ae (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    ∀ᵐ record ∂(P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x),
      P.experiment.transcriptLikelihood true record =
        if P.experiment.posteriorRecordDecision record then ENNReal.ofReal ((P.odds : ℝ) ^ m)
        else ENNReal.ofReal (((P.odds : ℝ) ^ m)⁻¹) := by
  filter_upwards [P.symmetricHitting_stoppedScore_abs_ae m hm x] with record hbound
  have hscore : P.experiment.stoppedWordScore record.2 =
      if P.experiment.posteriorRecordDecision record then (m : ℝ) * P.h else -((m : ℝ) * P.h) := by
    by_cases hs : 0 ≤ P.experiment.stoppedWordScore record.2
    · simpa only [BinaryExperiment.posteriorRecordDecision, hs, decide_true, ↓reduceIte,
        abs_of_nonneg hs] using hbound
    · have hn := lt_of_not_ge hs
      simp only [BinaryExperiment.posteriorRecordDecision, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [abs_of_neg hn] at hbound
      linarith
  have hlike : P.experiment.wordLikelihood true record.2 = Real.exp (P.experiment.stoppedWordScore record.2) := by
    rw [P.stoppedWordScore_eq_wordLogLikelihood, ← P.experiment.log_wordLikelihood,
      Real.exp_log (P.experiment.wordLikelihood_pos true record.2)]
  unfold BinaryExperiment.transcriptLikelihood
  rw [hlike, hscore]
  cases hd : P.experiment.posteriorRecordDecision record <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Real.exp_neg, P.exp_endpointThreshold]

def hittingDecisionEvent (P : Parameters) (bit : Bool) : Set (Unit × P.experiment.StoppedWord) :=
  {record | P.experiment.posteriorRecordDecision record = bit}

theorem measurableSet_hittingDecisionEvent (P : Parameters) (bit : Bool) :
    MeasurableSet (P.hittingDecisionEvent bit) :=
  P.experiment.measurable_posteriorRecordDecision (measurableSet_singleton bit)

theorem hittingDecisionEvent_compl (P : Parameters) :
    (P.hittingDecisionEvent true)ᶜ = P.hittingDecisionEvent false := by
  ext record
  cases h : P.experiment.posteriorRecordDecision record <;> simp [hittingDecisionEvent, h]

theorem symmetricHitting_decision_mass_change (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (bit : Bool) :
    P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) true
      (P.hittingDecisionEvent bit) =
    ENNReal.ofReal (if bit then (P.odds : ℝ) ^ m else ((P.odds : ℝ) ^ m)⁻¹) *
      P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) false
        (P.hittingDecisionEvent bit) := by
  rw [P.experiment.transcriptLaw_withDensity (Measure.dirac ()) (P.symmetricHittingTest m) true
    (P.symmetricHittingTest_expectedSamples_finite m), withDensity_apply _ (P.measurableSet_hittingDecisionEvent bit)]
  calc
    _ = ∫⁻ _record in P.hittingDecisionEvent bit,
        ENNReal.ofReal (if bit then (P.odds : ℝ) ^ m else ((P.odds : ℝ) ^ m)⁻¹)
        ∂(P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) false) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (P.symmetricHitting_transcriptLikelihood_ae m hm false),
        ae_restrict_mem (P.measurableSet_hittingDecisionEvent bit)] with record hlike hrecord
      change P.experiment.posteriorRecordDecision record = bit at hrecord
      rw [hlike, hrecord]
      cases bit <;> rfl
    _ = _ := by simp

theorem hittingDecision_mass_sum (P : Parameters) (μ : Measure (Unit × P.experiment.StoppedWord))
    [IsProbabilityMeasure μ] :
    μ (P.hittingDecisionEvent true) + μ (P.hittingDecisionEvent false) = 1 := by
  simpa only [P.hittingDecisionEvent_compl, measure_univ] using
    (measure_add_measure_compl (μ := μ) (P.measurableSet_hittingDecisionEvent true))

theorem hittingDecision_real_mass_sum (P : Parameters) (μ : Measure (Unit × P.experiment.StoppedWord))
    [IsProbabilityMeasure μ] :
    (μ (P.hittingDecisionEvent true)).toReal + (μ (P.hittingDecisionEvent false)).toReal = 1 := by
  have h := congrArg ENNReal.toReal (P.hittingDecision_mass_sum μ)
  rwa [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), ENNReal.toReal_one] at h

private theorem solve_two_boundary_masses {q a b : ℝ} (hq : 1 < q)
    (hsum : a + b = 1) (hweighted : q * a + q⁻¹ * b = 1) :
    a = 1 / (1 + q) ∧ q⁻¹ * b = 1 / (1 + q) := by
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans hq)
  have hw := congrArg (fun z : ℝ => q * z) hweighted
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul] at hw
  have hfactor : (q - 1) * ((1 + q) * a - 1) = 0 := by nlinarith
  have ha1 : (1 + q) * a = 1 := by
    have hz := (mul_eq_zero.mp hfactor).resolve_left (by linarith : q - 1 ≠ 0)
    linarith
  have ha : a = 1 / (1 + q) := (eq_div_iff (by linarith : 1 + q ≠ 0)).mpr (by nlinarith)
  refine ⟨ha, ?_⟩
  rw [← ha]
  have hb : b = q * a := by nlinarith
  rw [hb, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

theorem symmetricHitting_error_event_masses (P : Parameters) (m : ℕ) (hm : 1 ≤ m) :
    P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) false
        (P.hittingDecisionEvent true) = ENNReal.ofReal (P.endpointError m : ℝ) ∧
    P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) true
        (P.hittingDecisionEvent false) = ENNReal.ofReal (P.endpointError m : ℝ) := by
  let μ₀ := P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) false
  let μ₁ := P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) true
  let q : ℝ := (P.odds : ℝ) ^ m
  have ho : (1 : ℝ) < (P.odds : ℝ) := by exact_mod_cast P.odds_gt_one
  have hq : 1 < q := one_lt_pow₀ ho (by omega)
  have hpos : 0 ≤ (P.odds : ℝ) ^ m := (zero_lt_one.trans hq).le
  have hchange₁ : (μ₁ (P.hittingDecisionEvent true)).toReal = q * (μ₀ (P.hittingDecisionEvent true)).toReal := by
    simpa only [μ₀, μ₁, q, ↓reduceIte, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] using
      congrArg ENNReal.toReal (P.symmetricHitting_decision_mass_change m hm true)
  have hchange₀ : (μ₁ (P.hittingDecisionEvent false)).toReal = q⁻¹ * (μ₀ (P.hittingDecisionEvent false)).toReal := by
    simpa only [μ₀, μ₁, q, Bool.false_eq_true, ↓reduceIte, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hpos)] using
      congrArg ENNReal.toReal (P.symmetricHitting_decision_mass_change m hm false)
  have hweighted : q * (μ₀ (P.hittingDecisionEvent true)).toReal +
      q⁻¹ * (μ₀ (P.hittingDecisionEvent false)).toReal = 1 := by
    rw [← hchange₁, ← hchange₀]
    exact P.hittingDecision_real_mass_sum μ₁
  have hsol := solve_two_boundary_masses hq (P.hittingDecision_real_mass_sum μ₀) hweighted
  have hp : (P.endpointError m : ℝ) = 1 / (1 + q) := by
    simp only [endpointError, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_pow, q]
  constructor
  · change μ₀ (P.hittingDecisionEvent true) = _
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ₀ _), hsol.1, ← hp]
  · change μ₁ (P.hittingDecisionEvent false) = _
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ₁ _), hchange₀, hsol.2, ← hp]

theorem symmetricHitting_conditionalError_eq (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    P.experiment.conditionalError (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointError m : ℝ) := by
  have hset (x : Bool) : {record : Unit × P.experiment.StoppedWord |
      P.experiment.posteriorRecordDecision record ≠ x} = P.hittingDecisionEvent (!x) := by
    ext record
    cases x <;> cases hd : P.experiment.posteriorRecordDecision record <;> simp [hittingDecisionEvent, hd]
  change P.experiment.conditionalError (Measure.dirac ())
    (P.experiment.posteriorSPRT (P.endpointError m)) x = _
  rw [P.experiment.posteriorSPRT_conditionalError_transcript, hset]
  cases x
  · exact (P.symmetricHitting_error_event_masses m hm).1
  · exact (P.symmetricHitting_error_event_masses m hm).2

theorem symmetricHitting_record_error_mass (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x
      (P.hittingDecisionEvent (!x)) = ENNReal.ofReal (P.endpointError m : ℝ) := by
  cases x
  · exact (P.symmetricHitting_error_event_masses m hm).1
  · exact (P.symmetricHitting_error_event_masses m hm).2

theorem wordLogLikelihood_false_eq_neg_true (P : Parameters) (word : P.experiment.StoppedWord) :
    P.experiment.wordLogLikelihood false word = -P.experiment.wordLogLikelihood true word := by
  unfold BinaryExperiment.wordLogLikelihood
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Bool.not_false, Bool.not_true]
  rw [Real.log_div (P.experiment.channelReal_pos false _).ne' (P.experiment.channelReal_pos true _).ne',
    Real.log_div (P.experiment.channelReal_pos true _).ne' (P.experiment.channelReal_pos false _).ne']
  ring

theorem symmetricHitting_wordLogLikelihood_ae (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    ∀ᵐ record ∂(P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x),
      P.experiment.wordLogLikelihood x record.2 =
        if P.experiment.posteriorRecordDecision record = x then (m : ℝ) * P.h else -((m : ℝ) * P.h) := by
  filter_upwards [P.symmetricHitting_stoppedScore_abs_ae m hm x] with record hbound
  have hscore : P.experiment.stoppedWordScore record.2 =
      if P.experiment.posteriorRecordDecision record then (m : ℝ) * P.h else -((m : ℝ) * P.h) := by
    by_cases hs : 0 ≤ P.experiment.stoppedWordScore record.2
    · simpa only [BinaryExperiment.posteriorRecordDecision, hs, decide_true, ↓reduceIte,
        abs_of_nonneg hs] using hbound
    · have hn := lt_of_not_ge hs
      simp only [BinaryExperiment.posteriorRecordDecision, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [abs_of_neg hn] at hbound
      linarith
  have htrue : P.experiment.wordLogLikelihood true record.2 =
      if P.experiment.posteriorRecordDecision record then (m : ℝ) * P.h else -((m : ℝ) * P.h) := by
    rw [← P.stoppedWordScore_eq_wordLogLikelihood]
    exact hscore
  cases x
  · rw [P.wordLogLikelihood_false_eq_neg_true, htrue]
    cases hd : P.experiment.posteriorRecordDecision record <;> simp
  · exact htrue

theorem symmetricHitting_integral_wordLogLikelihood_transcript (P : Parameters) (m : ℕ)
    (hm : 1 ≤ m) (x : Bool) :
    (∫ record, P.experiment.wordLogLikelihood x record.2
      ∂(P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x)) =
      (m : ℝ) * P.h * (1 - 2 * (P.endpointError m : ℝ)) := by
  let μ := P.experiment.transcriptLaw (Measure.dirac ()) (P.symmetricHittingTest m) x
  let B : ℝ := (m : ℝ) * P.h
  have heq : (fun record : Unit × P.experiment.StoppedWord =>
      if P.experiment.posteriorRecordDecision record = x then B else -B) =
      fun record => B + (P.hittingDecisionEvent (!x)).indicator (fun _ => -2 * B) record := by
    funext record
    cases x <;> cases hd : P.experiment.posteriorRecordDecision record <;>
      simp [hittingDecisionEvent, hd] <;> ring
  have hreal : μ.real (P.hittingDecisionEvent (!x)) = (P.endpointError m : ℝ) := by
    change (μ (P.hittingDecisionEvent (!x))).toReal = _
    rw [P.symmetricHitting_record_error_mass m hm x, ENNReal.toReal_ofReal]
    exact_mod_cast (P.endpointError_pos m).le
  have htotal : μ.real Set.univ = 1 := by
    change (μ Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  rw [integral_congr_ae (P.symmetricHitting_wordLogLikelihood_ae m hm x)]
  change (∫ record, if P.experiment.posteriorRecordDecision record = x then B else -B ∂μ) = _
  rw [heq, integral_add (integrable_const B)
    ((integrable_const (-2 * B)).indicator (P.measurableSet_hittingDecisionEvent (!x))),
    integral_const, integral_indicator_const _ (P.measurableSet_hittingDecisionEvent (!x))]
  simp only [htotal, smul_eq_mul, one_mul]
  rw [hreal]
  dsimp only [B]
  ring

theorem symmetricHitting_integral_stoppedSum (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    (∫ sample, P.experiment.wordLogLikelihood x
      (P.experiment.stoppedTranscript (P.symmetricHittingTest m) sample).2
      ∂(P.experiment.conditionalLaw (Measure.dirac ()) x)) =
      (m : ℝ) * P.h * (1 - 2 * (P.endpointError m : ℝ)) := by
  rw [← P.symmetricHitting_integral_wordLogLikelihood_transcript m hm x]
  unfold BinaryExperiment.transcriptLaw
  symm
  exact integral_map (P.experiment.measurable_stoppedTranscript (P.symmetricHittingTest m)).aemeasurable
    ((measurable_of_countable (P.experiment.wordLogLikelihood x)).comp measurable_snd).aestronglyMeasurable

theorem symmetricHitting_expectedSamples_eq (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    P.experiment.expectedSamples (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointMeanCount m : ℝ) := by
  have hf := P.symmetricHittingTest_expectedSamples_finite m x
  have hw := P.experiment.integral_stoppedSum_wald (Measure.dirac ()) (P.symmetricHittingTest m) x hf
  rw [P.symmetricHitting_integral_stoppedSum m hm x, P.divergence_eq_kappa] at hw
  have he : (P.experiment.expectedSamples (Measure.dirac ()) (P.symmetricHittingTest m) x).toReal =
      ((m : ℝ) * P.h * (1 - 2 * (P.endpointError m : ℝ))) / P.kappa := by
    apply (eq_div_iff P.kappa_pos.ne').mpr
    nlinarith [hw]
  have hreal : (P.experiment.expectedSamples (Measure.dirac ()) (P.symmetricHittingTest m) x).toReal =
      (P.endpointMeanCount m : ℝ) := by
    rw [he]
    unfold endpointMeanCount kappa
    push_cast
    have hg : (P.gamma : ℝ) ≠ 0 := by exact_mod_cast P.gamma_pos.ne'
    field_simp [hg, P.h_pos.ne']
  exact (ENNReal.ofReal_toReal hf).symm.trans (congrArg ENNReal.ofReal hreal)

theorem symmetricHitting_expectedCharge_eq (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    P.experiment.expectedObservationCharge (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointCharge m : ℝ) := by
  rw [P.experiment.expectedObservationCharge_eq, P.symmetricHitting_expectedSamples_eq m hm x]
  change ENNReal.ofReal (P.reviewFee : ℝ) * ENNReal.ofReal (P.endpointMeanCount m : ℝ) = _
  have hc : 0 ≤ (P.reviewFee : ℝ) := by exact_mod_cast P.reviewFee_pos.le
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  exact (Rat.cast_mul _ _).symm

theorem symmetricHitting_expectedCharge_eq_information (P : Parameters) (m : ℕ) (hm : 1 ≤ m) (x : Bool) :
    P.experiment.expectedObservationCharge (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal P.a * phi (P.endpointError m : ℝ) :=
  (P.symmetricHitting_expectedCharge_eq m hm x).trans (P.endpointChargeENN_eq_information m)

/-- The actual D04 law, for every original m≥1 and either truth. In
particular p_m is not required to be at most 1/4. -/
theorem symmetricHittingExactLaw (P : Parameters) : P.SymmetricHittingExactLaw := by
  intro m hm
  exact ⟨P.symmetricHitting_conditionalError_eq m hm,
    P.symmetricHitting_expectedSamples_eq m hm, P.symmetricHitting_expectedCharge_eq m hm⟩

end PaperProofs.Statistics.BinarySymmetric.Parameters
