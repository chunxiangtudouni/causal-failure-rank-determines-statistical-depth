module

public import PaperProofs.Common.NativeHeadAccounting

/-! The original local Bayes objective on the SAME native product world.
Private seeds, non-MAP decisions and infinite observation charges remain.
This module supplies expectation identities, not a Bellman assumption. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

theorem lintegral_localStage_seededWorld (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : Seed × input.StageSample stage → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample, f (sample.1, sample.2 stage) ∂input.seededWorldLaw ν) =
      ∑ truth : Bool, (input.experiment stage).priorMass truth *
        ∫⁻ sample, f (sample.1, (truth, sample.2)) ∂(input.experiment stage).conditionalLaw ν truth := by
  let E := input.experiment stage
  let g : input.StageSample stage → ℝ≥0∞ := fun localSample => ∫⁻ seed, f (seed, localSample) ∂ν
  have hg : Measurable g := (hf.comp measurable_swap).lintegral_prod_right'
  have hworld : Measurable (fun sample : Seed × input.World => f (sample.1, sample.2 stage)) :=
    hf.comp (measurable_fst.prodMk ((measurable_pi_apply stage).comp measurable_snd))
  have hp (truth : Bool) :
      (∫⁻ localSample, g localSample ∂(Measure.dirac truth).prod (E.tapeLaw truth)) =
        ∫⁻ sample, f (sample.1, (truth, sample.2)) ∂E.conditionalLaw ν truth := by
    rw [Measure.dirac_prod, lintegral_map hg measurable_prodMk_left]
    exact (lintegral_prod_symm (fun sample : Seed × E.Tape => f (sample.1, (truth, sample.2)))
      (hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).aemeasurable).symm
  rw [StatisticalInput.seededWorldLaw, lintegral_prod_symm _ hworld.aemeasurable]
  change (∫⁻ world, g (world stage) ∂input.worldLaw) = _
  rw [← lintegral_map hg (measurable_pi_apply stage), input.worldLaw_coordinate,
    StatisticalInput.stageLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul, Fintype.sum_bool]
  rw [hp true, hp false]

theorem bayesError_eq_seededWorld_integral (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : (input.experiment stage).AdmissibleRule Seed) :
    (input.experiment stage).bayesError ν test =
      ∫⁻ sample, (if test.rule.decision sample.1 (worldTapes input sample.2 stage) ≠
        input.truthAt sample.2 stage then (1 : ℝ≥0∞) else 0) ∂input.seededWorldLaw ν := by
  classical
  let E := input.experiment stage
  let f : Seed × input.StageSample stage → ℝ≥0∞ := fun sample =>
    if test.rule.decision sample.1 sample.2.2 ≠ sample.2.1 then 1 else 0
  have hdecision : Measurable (fun sample : Seed × input.StageSample stage => test.rule.decision sample.1 sample.2.2) :=
    test.measurable_decision.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have herr : MeasurableSet {sample : Seed × input.StageSample stage | test.rule.decision sample.1 sample.2.2 ≠ sample.2.1} :=
    (measurableSet_eq_fun hdecision (measurable_fst.comp measurable_snd)).compl
  have hf : Measurable f := Measurable.ite herr measurable_const measurable_const
  have h := lintegral_localStage_seededWorld input stage ν f hf
  have hp (truth : Bool) : (∫⁻ sample, f (sample.1, (truth, sample.2)) ∂E.conditionalLaw ν truth) =
      E.conditionalError ν test truth := by
    have hm : MeasurableSet {sample : Seed × E.Tape | test.rule.decision sample.1 sample.2 ≠ truth} :=
      (test.measurable_decision (measurableSet_singleton truth)).compl
    simpa only [f, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply,
      BinaryExperiment.conditionalError] using
      (lintegral_indicator_one (μ := E.conditionalLaw ν truth) hm)
  calc
    E.bayesError ν test = ∑ truth : Bool, E.priorMass truth *
        ∫⁻ sample, f (sample.1, (truth, sample.2)) ∂E.conditionalLaw ν truth := by
      unfold BinaryExperiment.bayesError
      apply Finset.sum_congr rfl
      intro truth _
      rw [hp]
    _ = ∫⁻ sample, f (sample.1, sample.2 stage) ∂input.seededWorldLaw ν := h.symm
    _ = _ := by
      apply lintegral_congr
      intro sample
      have htape : (sample.2 stage).2 = worldTapes input sample.2 stage := by funext n; rfl
      dsimp only [f]
      rw [htape]
      split_ifs <;> simp_all only [StatisticalInput.truthAt]

theorem bayesObjective_eq_seededWorld_integral (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : (input.experiment stage).AdmissibleRule Seed)
    (penalty : ℝ≥0∞) :
    (input.experiment stage).bayesObjective ν test penalty =
      ∫⁻ sample, (input.experiment stage).observationCharge
          (test.rule.stop sample.1 (worldTapes input sample.2 stage)) +
        penalty * (if test.rule.decision sample.1 (worldTapes input sample.2 stage) ≠
          input.truthAt sample.2 stage then (1 : ℝ≥0∞) else 0) ∂input.seededWorldLaw ν := by
  classical
  have hlocal : Measurable (fun sample : Seed × input.World => (sample.1, worldTapes input sample.2 stage)) :=
    measurable_fst.prodMk (((measurable_pi_apply stage).comp measurable_snd).snd)
  have hobs : Measurable (fun sample : Seed × input.World => (input.experiment stage).observationCharge
      (test.rule.stop sample.1 (worldTapes input sample.2 stage))) :=
    (measurable_of_countable (input.experiment stage).observationCharge).comp
    (test.measurable_stop.comp hlocal)
  have herr : MeasurableSet {sample : Seed × input.World |
      test.rule.decision sample.1 (worldTapes input sample.2 stage) ≠ input.truthAt sample.2 stage} :=
    (measurableSet_eq_fun (test.measurable_decision.comp hlocal)
      ((input.measurable_truthAt stage).comp measurable_snd)).compl
  have herror : Measurable (fun sample : Seed × input.World =>
      if test.rule.decision sample.1 (worldTapes input sample.2 stage) ≠ input.truthAt sample.2 stage
        then (1 : ℝ≥0∞) else 0) := Measurable.ite herr measurable_const measurable_const
  rw [BinaryExperiment.bayesObjective, bayesObservationCharge_eq_seededWorld_integral,
    bayesError_eq_seededWorld_integral, ← lintegral_const_mul penalty herror,
    ← lintegral_add_left hobs]

/-- Adding the independent good price to the local difference penalty is
exactly the original good/bad decision weight, including infinite charge. -/
theorem shiftedBayesObjective_eq_seededWorld_integral (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : (input.experiment stage).AdmissibleRule Seed)
    (good bad : ℝ) (hgood : 0 ≤ good) (horder : good ≤ bad) :
    ENNReal.ofReal good + (input.experiment stage).bayesObjective ν test (ENNReal.ofReal (bad - good)) =
      ∫⁻ sample, (input.experiment stage).observationCharge
          (test.rule.stop sample.1 (worldTapes input sample.2 stage)) +
        (if test.rule.decision sample.1 (worldTapes input sample.2 stage) = input.truthAt sample.2 stage
          then ENNReal.ofReal good else ENNReal.ofReal bad) ∂input.seededWorldLaw ν := by
  classical
  rw [bayesObjective_eq_seededWorld_integral]
  have hconstant : (∫⁻ _sample : Seed × input.World, ENNReal.ofReal good ∂input.seededWorldLaw ν) = ENNReal.ofReal good := by
    simp only [lintegral_const, measure_univ, mul_one]
  have hmconstant : Measurable (fun _sample : Seed × input.World => ENNReal.ofReal good) := measurable_const
  rw [← hconstant, ← lintegral_add_left hmconstant]
  apply lintegral_congr
  intro sample
  by_cases hc : test.rule.decision sample.1 (worldTapes input sample.2 stage) = input.truthAt sample.2 stage
  · simp only [hc, ne_eq, not_true_eq_false, ite_false, ite_true, mul_zero, add_zero]
    rw [hconstant]
    ac_rfl
  · simp only [hc, ne_eq, not_false_eq_true, ite_false, ite_true, mul_one]
    have hsum : ENNReal.ofReal good + ENNReal.ofReal (bad - good) = ENNReal.ofReal bad := by
      rw [← ENNReal.ofReal_add hgood (sub_nonneg.mpr horder)]
      congr 1
      ring
    calc
      _ = (input.experiment stage).observationCharge
          (test.rule.stop sample.1 (worldTapes input sample.2 stage)) +
            (ENNReal.ofReal good + ENNReal.ofReal (bad - good)) := by ac_rfl
      _ = _ := by rw [hsum]

theorem nativeHead_shiftedBayesObjective_eq (input : StatisticalInput I) (head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (input.goodPenaltyReal head R price) +
      (input.experiment head).bayesObjective ν (nativeHeadTest input head rule hm)
        (ENNReal.ofReal (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) =
      ∫⁻ sample, (input.experiment head).observationCharge
          (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) +
        nativeHeadContinuationWeight input head R price rule sample ∂input.seededWorldLaw ν := by
  have ho := input.penalty_successor_order head R price hprice
  rw [shiftedBayesObjective_eq_seededWorld_integral input head ν (nativeHeadTest input head rule hm)
    (input.goodPenaltyReal head R price) (input.badPenaltyReal head R price) ho.1 ho.2.1]
  apply lintegral_congr
  intro sample
  dsimp only [nativeHeadTest]
  unfold nativeHeadContinuationWeight
  by_cases hc : headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
  · simp only [hc, ite_true]
  · simp only [hc, ite_false]

end PaperProofs.Common.Native

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type} [MeasurableSpace Seed]

/-- The final infimum comparison uses its actual Type0 seed index. All
preceding identities permit arbitrary seed universes; the native comparator's
already-proved seed encoding retains the full arbitrary-universe class. -/
theorem nativeHead_localValue_lower (input : StatisticalInput I) (head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (input.goodPenaltyReal head R price +
      (input.experiment head).localValueReal
        (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      ∫⁻ sample, (input.experiment head).observationCharge
          (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) +
        nativeHeadContinuationWeight input head R price rule sample ∂input.seededWorldLaw ν := by
  let E := input.experiment head
  let gap := input.badPenaltyReal head R price - input.goodPenaltyReal head R price
  have ho := input.penalty_successor_order head R price hprice
  have hj : ENNReal.ofReal (E.localValueReal gap) = E.localValue (ENNReal.ofReal gap) :=
    ENNReal.ofReal_toReal (E.localValue_ofReal_ne_top gap)
  calc
    _ = ENNReal.ofReal (input.goodPenaltyReal head R price) + E.localValue (ENNReal.ofReal gap) := by
      rw [ENNReal.ofReal_add ho.1 (E.localValueReal_nonneg gap), hj]
    _ ≤ ENNReal.ofReal (input.goodPenaltyReal head R price) +
        E.bayesObjective ν (nativeHeadTest input head rule hm) (ENNReal.ofReal gap) :=
      add_le_add le_rfl (E.localValue_le_test ν (nativeHeadTest input head rule hm) _)
    _ = _ := nativeHead_shiftedBayesObjective_eq input head R price hprice rule hm ν

end PaperProofs.Common.Native
