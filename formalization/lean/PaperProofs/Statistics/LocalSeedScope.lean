module

public import PaperProofs.Statistics.LocalTest

/-!
Scope bridge for B02, frozen price-proofs.tex:5--12. The original local
infimum is not changed. Tonelli disintegrates the exact nonnegative objective
over the original independent private seed, including infinite charges and
infinite penalties. Fixing a seed preserves the original stopped decision,
so a Type-0 deterministic test already supplies the required lower bound
for every measurable randomized test in every seed universe.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Statistics.BinaryExperiment

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Freeze the original private seed, preserving the exact stopping rule and decision. -/
def fixedSeedTest (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (seed : Seed) : E.AdmissibleRule Unit where
  rule := {
    stop := fun _ tape => test.rule.stop seed tape
    decision := fun _ tape => test.rule.decision seed tape
    stopping := fun _ => test.rule.stopping seed
    stoppedDecision := fun _ => test.rule.stoppedDecision seed
  }
  measurable_stop := test.measurable_stop.comp (measurable_const.prodMk measurable_snd)
  measurable_decision := test.measurable_decision.comp (measurable_const.prodMk measurable_snd)

theorem fixedSeedTest_observationCharge (E : BinaryExperiment)
    (test : E.AdmissibleRule Seed) (seed : Seed) (truth : Bool) :
    E.expectedObservationCharge (Measure.dirac ()) (E.fixedSeedTest test seed) truth =
      ∫⁻ tape, E.observationCharge (test.rule.stop seed tape) ∂E.tapeLaw truth := by
  have hm : Measurable (fun sample : Unit × E.Tape =>
      E.observationCharge (test.rule.stop seed sample.2)) :=
    (measurable_of_countable E.observationCharge).comp
      (test.measurable_stop.comp (measurable_const.prodMk measurable_snd))
  change (∫⁻ sample : Unit × E.Tape,
    E.observationCharge (test.rule.stop seed sample.2)
      ∂((Measure.dirac ()).prod (E.tapeLaw truth))) = _
  rw [lintegral_prod _ hm.aemeasurable]
  simp

theorem fixedSeedTest_error (E : BinaryExperiment)
    (test : E.AdmissibleRule Seed) (seed : Seed) (truth : Bool) :
    E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) truth =
      E.tapeLaw truth {tape | test.rule.decision seed tape ≠ truth} := by
  change (Measure.dirac ()).prod (E.tapeLaw truth)
    {sample : Unit × E.Tape | test.rule.decision seed sample.2 ≠ truth} = _
  have hs : {sample : Unit × E.Tape | test.rule.decision seed sample.2 ≠ truth} =
      Set.univ ×ˢ {tape | test.rule.decision seed tape ≠ truth} := by
    ext sample
    simp
  rw [hs, Measure.prod_prod, measure_univ, one_mul]

theorem measurable_fixedSeedTest_charge (E : BinaryExperiment)
    (test : E.AdmissibleRule Seed) (truth : Bool) :
    Measurable (fun seed =>
      E.expectedObservationCharge (Measure.dirac ()) (E.fixedSeedTest test seed) truth) := by
  simp_rw [fixedSeedTest_observationCharge]
  exact ((measurable_of_countable E.observationCharge).comp
    test.measurable_stop).lintegral_prod_right'

theorem measurable_fixedSeedTest_error (E : BinaryExperiment)
    (test : E.AdmissibleRule Seed) (truth : Bool) :
    Measurable (fun seed =>
      E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) truth) := by
  simp_rw [fixedSeedTest_error]
  have hs : MeasurableSet {sample : Seed × E.Tape |
      test.rule.decision sample.1 sample.2 ≠ truth} :=
    ((measurableSet_singleton truth).preimage test.measurable_decision).compl
  exact measurable_measure_prodMk_left hs

theorem observationCharge_eq_seed_integral (E : BinaryExperiment)
    (ν : Measure Seed) (test : E.AdmissibleRule Seed) (truth : Bool) :
    E.expectedObservationCharge ν test truth =
      ∫⁻ seed, E.expectedObservationCharge (Measure.dirac ())
        (E.fixedSeedTest test seed) truth ∂ν := by
  simp_rw [fixedSeedTest_observationCharge]
  exact lintegral_prod _ (((measurable_of_countable E.observationCharge).comp
    test.measurable_stop).aemeasurable)

theorem conditionalError_eq_seed_integral (E : BinaryExperiment)
    (ν : Measure Seed) (test : E.AdmissibleRule Seed) (truth : Bool) :
    E.conditionalError ν test truth =
      ∫⁻ seed, E.conditionalError (Measure.dirac ())
        (E.fixedSeedTest test seed) truth ∂ν := by
  simp_rw [fixedSeedTest_error]
  have hs : MeasurableSet {sample : Seed × E.Tape |
      test.rule.decision sample.1 sample.2 ≠ truth} :=
    ((measurableSet_singleton truth).preimage test.measurable_decision).compl
  exact Measure.prod_apply hs

theorem bayesObjective_eq_seed_integral (E : BinaryExperiment)
    (ν : Measure Seed) (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞) :
    E.bayesObjective ν test penalty =
      ∫⁻ seed, E.bayesObjective (Measure.dirac ())
        (E.fixedSeedTest test seed) penalty ∂ν := by
  have hc (truth : Bool) := E.measurable_fixedSeedTest_charge test truth
  have he (truth : Bool) := E.measurable_fixedSeedTest_error test truth
  have hcs : Measurable (fun seed =>
      E.priorMass true * E.expectedObservationCharge (Measure.dirac ()) (E.fixedSeedTest test seed) true +
      E.priorMass false * E.expectedObservationCharge (Measure.dirac ()) (E.fixedSeedTest test seed) false) :=
    ((hc true).const_mul (E.priorMass true)).add ((hc false).const_mul (E.priorMass false))
  have hes : Measurable (fun seed =>
      E.priorMass true * E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) true +
      E.priorMass false * E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) false) :=
    ((he true).const_mul (E.priorMass true)).add ((he false).const_mul (E.priorMass false))
  simp only [bayesObjective, bayesObservationCharge, bayesError, Fintype.sum_bool]
  rw [lintegral_add_left hcs
    (fun seed => penalty *
      (E.priorMass true * E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) true +
        E.priorMass false * E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) false))]
  rw [lintegral_add_left ((hc true).const_mul (E.priorMass true))
    (fun seed => E.priorMass false *
      E.expectedObservationCharge (Measure.dirac ()) (E.fixedSeedTest test seed) false),
    lintegral_const_mul _ (hc true), lintegral_const_mul _ (hc false)]
  rw [lintegral_const_mul penalty hes]
  rw [lintegral_add_left ((he true).const_mul (E.priorMass true))
    (fun seed => E.priorMass false *
      E.conditionalError (Measure.dirac ()) (E.fixedSeedTest test seed) false),
    lintegral_const_mul _ (he true), lintegral_const_mul _ (he false)]
  rw [← observationCharge_eq_seed_integral, ← observationCharge_eq_seed_integral,
    ← conditionalError_eq_seed_integral, ← conditionalError_eq_seed_integral]

/-- The original local infimum bounds every measurable randomized test in any universe.
No finite expected charge, MAP, or optimizer assumption is used. -/
theorem localValue_le_test_any_seed (E : BinaryExperiment)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (penalty : ℝ≥0∞) :
    E.localValue penalty ≤ E.bayesObjective ν test penalty := by
  rw [bayesObjective_eq_seed_integral]
  have hp (seed : Seed) : E.localValue penalty ≤
      E.bayesObjective (Measure.dirac ()) (E.fixedSeedTest test seed) penalty :=
    E.localValue_le_test (Measure.dirac ()) (E.fixedSeedTest test seed) penalty
  simpa using (lintegral_mono hp :
    (∫⁻ _ : Seed, E.localValue penalty ∂ν) ≤ _)

/-- Randomization does not change this unconstrained linear penalty infimum.
This is an equality of infima; no minimizing test is selected. -/
theorem localValue_eq_deterministic (E : BinaryExperiment) (penalty : ℝ≥0∞) :
    E.localValue penalty =
      ⨅ test : E.AdmissibleRule Unit, E.bayesObjective (Measure.dirac ()) test penalty := by
  apply le_antisymm
  · exact le_iInf fun test => E.localValue_le_test (Measure.dirac ()) test penalty
  · unfold localValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => le_iInf fun test => ?_
    let : IsProbabilityMeasure ν := hν
    rw [bayesObjective_eq_seed_integral]
    have hp (seed : SmallSeed) :
        (⨅ test : E.AdmissibleRule Unit, E.bayesObjective (Measure.dirac ()) test penalty) ≤
          E.bayesObjective (Measure.dirac ()) (E.fixedSeedTest test seed) penalty :=
      iInf_le _ _
    simpa using (lintegral_mono hp :
      (∫⁻ _ : SmallSeed,
        (⨅ test : E.AdmissibleRule Unit, E.bayesObjective (Measure.dirac ()) test penalty) ∂ν) ≤ _)

end PaperProofs.Statistics.BinaryExperiment
