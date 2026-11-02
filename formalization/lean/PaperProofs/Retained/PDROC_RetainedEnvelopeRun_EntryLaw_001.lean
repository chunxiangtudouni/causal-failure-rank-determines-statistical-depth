module

public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics

namespace PDROC.RetainedEnvelopeRun.EntryLaw

variable {I : Instance}

/-- The actual first-entry atom is independent of this stage's complete
truth and potential tape. Infinite integrands and zero-mass atoms are kept. -/
theorem lintegral_on_entry_stageFunction
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Unit)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (f : input.StageSample stage → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample in {sample | entryHistory input C mode accounting policy.rule stage sample = some history},
      f (sample.2 stage) ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C mode accounting policy.rule stage sample = some history} *
          ∫⁻ localSample, f localSample ∂input.stageLaw stage := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C mode accounting policy.rule stage
  let atom : Set (Unit × EntryHistory I) := {((), some history)}
  let weight : Unit × EntryHistory I → ℝ≥0∞ := atom.indicator (fun _ => 1)
  let joint := fun sample : Unit × input.World => (record sample, sample.2 stage)
  let g : (Unit × EntryHistory I) × input.StageSample stage → ℝ≥0∞ := fun z => weight z.1 * f z.2
  have hr : Measurable record :=
    measurable_entrySeedHistory input C mode accounting policy.rule policy.measurable_rule stage
  have hevent : MeasurableSet {sample | entryHistory input C mode accounting policy.rule stage sample = some history} :=
    (measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule stage)
      (measurableSet_singleton (some history))
  have hj : Measurable joint := hr.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hw : Measurable weight := measurable_const.indicator (measurableSet_singleton _)
  have hg : Measurable g := (hw.comp measurable_fst).mul (hf.comp measurable_snd)
  have hpoint : ∀ sample : Unit × input.World,
      {sample | entryHistory input C mode accounting policy.rule stage sample = some history}.indicator
        (fun x => f (x.2 stage)) sample = g (joint sample) := by
    intro sample
    cases hu : sample.1
    by_cases he : entryHistory input C mode accounting policy.rule stage sample = some history
    · have hm : sample ∈ {sample | entryHistory input C mode accounting policy.rule stage sample = some history} := he
      rw [Set.indicator_of_mem hm]
      have hrval : record sample = ((), some history) := by simp only [record, entrySeedHistory, hu, he]
      simp only [g, joint, weight, hrval, atom, Set.indicator_of_mem (Set.mem_singleton _), one_mul]
    · have hm : sample ∉ {sample | entryHistory input C mode accounting policy.rule stage sample = some history} := he
      rw [Set.indicator_of_notMem hm]
      have hrval : record sample ∉ atom := by
        intro hh
        have hc : entryHistory input C mode accounting policy.rule stage sample = some history :=
          congrArg Prod.snd (Set.mem_singleton_iff.mp hh)
        exact he hc
      simp only [g, joint, weight, Set.indicator_of_notMem hrval, zero_mul]
  have hmass : (μ.map record) atom =
      μ {sample | entryHistory input C mode accounting policy.rule stage sample = some history} := by
    rw [Measure.map_apply hr (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C mode accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and]
    rfl
  calc
    _ = ∫⁻ sample, g (joint sample) ∂μ := by
      rw [← lintegral_indicator hevent]
      exact lintegral_congr hpoint
    _ = ∫⁻ z, g z ∂μ.map joint := (lintegral_map hg hj).symm
    _ = ∫⁻ z, g z ∂(μ.map record).prod (input.stageLaw stage) := by
      rw [entrySeedHistory_jointLaw input C mode accounting policy (Measure.dirac ()) stage]
    _ = (∫⁻ r, weight r ∂μ.map record) * ∫⁻ x, f x ∂input.stageLaw stage :=
      lintegral_prod_mul hw.aemeasurable hf.aemeasurable
    _ = _ := by
      rw [show (∫⁻ r, weight r ∂μ.map record) = (μ.map record) atom by
        exact (lintegral_indicator_const (measurableSet_singleton _) 1).trans (one_mul _)]
      rw [hmass]

/-- The fixed original potential-tape stopping charge has exactly its
original Bayes expectation. No finite-charge or target-range premise. -/
theorem stageLaw_posteriorObservationCharge (input : StatisticalInput I) (stage : I.Stage) (p : ℚ) :
    (∫⁻ sample : input.StageSample stage,
      (input.experiment stage).observationCharge
        ((input.experiment stage).posteriorThresholdStop p sample.2) ∂input.stageLaw stage) =
      (input.experiment stage).bayesObservationCharge (Measure.dirac ())
        ((input.experiment stage).posteriorSPRT p) :=
  stageLaw_testObservationCharge input stage ((input.experiment stage).posteriorSPRT p)

/-- The precise local-price integral needed after proving actual count
domination. The gate is the actual full first-entry history, never success. -/
theorem lintegral_on_entry_posteriorObservationCharge
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Unit)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ) :
    (∫⁻ sample in {sample | entryHistory input C mode accounting policy.rule stage sample = some history},
      (input.experiment stage).observationCharge
        ((input.experiment stage).posteriorThresholdStop p (sample.2 stage).2)
      ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C mode accounting policy.rule stage sample = some history} *
          (input.experiment stage).bayesObservationCharge (Measure.dirac ())
            ((input.experiment stage).posteriorSPRT p) := by
  have h := lintegral_on_entry_stageFunction input C mode accounting policy stage history
    (stageTestObservationCharge input stage ((input.experiment stage).posteriorSPRT p))
    (measurable_stageTestObservationCharge input stage ((input.experiment stage).posteriorSPRT p))
  rw [stageLaw_testObservationCharge] at h
  exact h

end PDROC.RetainedEnvelopeRun.EntryLaw
