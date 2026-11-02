module
public import PaperProofs.Paid.PDROC_LocalRecord_013

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def simulatorDrawPair (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (record : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.StoppedWord) :
    (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance :=
  (record.1, simulatorDrawDecoder P fee hfee source stage record)

theorem measurable_simulatorDrawPair (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorDrawPair P fee hfee source stage) :=
  measurable_fst.prodMk (measurable_simulatorDrawDecoder P fee hfee source hm stage)

/-- The true stopped-law image keeps the complete original private seed,
virtual entry history, full finite observation record, and terminal action. -/
noncomputable def simulatorDrawLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) :
    Measure ((Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance) :=
  (P.binarySymmetric.bayesStoppedLaw ν (simulatorLocalTest P fee hfee source hm stage)).map
    (simulatorDrawPair P fee hfee source stage)

/-- The simulator record posterior is derived from the REAL stopped-law
posterior identity and exact full-word recovery. No record/test field is
assumed to have this law, and no future truth is put into the seed. -/
theorem simulatorDrawLaw_posterior (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) (truth : Bool) :
    (simulatorDrawLaw P fee hfee source hm stage ν).withDensity
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P record.2.record))) =
      (1 / 2 : ℝ≥0∞) •
        (P.binarySymmetric.experiment.transcriptLaw ν (simulatorLocalTest P fee hfee source hm stage) truth).map
          (simulatorDrawPair P fee hfee source stage) := by
  have hg := measurable_simulatorDrawPair P fee hfee source hm stage
  have hd : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P record.2.record))) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P draw.record)))).comp measurable_snd
  have h := map_withDensity_comp (P.binarySymmetric.bayesStoppedLaw ν (simulatorLocalTest P fee hfee source hm stage))
    (simulatorDrawPair P fee hfee source stage) hg _ hd
  have hid : (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.StoppedWord =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth
        (auxiliaryRecordWord P ((simulatorDrawPair P fee hfee source stage) record).2.record))) =
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth record.2)) := by
    funext record
    rw [simulatorDrawPair, simulatorDrawDecoder_word]
  rw [hid, P.binarySymmetric.bayesStoppedLaw_posterior_withDensity ν _ hf truth,
    Measure.map_smul (1 / 2 : ℝ≥0∞) hg.aemeasurable] at h
  exact h.symm

/-- Exact source test fee as the mean Cm of actual source draw records,
including records which select abandonment or a non-MAP write. -/
theorem simulatorDrawLaw_endpointCharge_mean (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    P.binarySymmetric.experiment.bayesObservationCharge ν (simulatorLocalTest P fee hfee source hm stage) =
      ∫⁻ record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance,
        ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.record.level : ℝ)
          ∂simulatorDrawLaw P fee hfee source hm stage ν := by
  rw [bayesObservationCharge_eq_mean_endpointCharge P.binarySymmetric ν _ hf, simulatorDrawLaw]
  have hCm : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.record.level : ℝ)) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance =>
      ENNReal.ofReal (P.binarySymmetric.endpointCharge draw.record.level : ℝ))).comp measurable_snd
  rw [lintegral_map hCm (measurable_simulatorDrawPair P fee hfee source hm stage)]
  apply lintegral_congr
  intro record
  have hscore : wordSignedScore P.binarySymmetric record.2 =
      (simulatorDrawDecoder P fee hfee source stage record).record.score := by
    rw [← simulatorDrawDecoder_word P fee hfee source stage record]
    exact auxiliaryRecord_wordSignedScore P _
  change ENNReal.ofReal (P.binarySymmetric.endpointCharge (wordSignedScore P.binarySymmetric record.2).natAbs : ℝ) =
    ENNReal.ofReal (P.binarySymmetric.endpointCharge
      (simulatorDrawDecoder P fee hfee source stage record).record.score.natAbs : ℝ)
  rw [hscore]

/-- Conditional law of the ACTUAL Option draw sampler, retaining genuine
nonreturn in its definition and proving it null from finite local ET. -/
theorem simulatorDrawAt_conditionalLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) (truth : Bool)
    (hf : P.binarySymmetric.experiment.expectedSamples ν (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    (P.binarySymmetric.experiment.conditionalLaw ν truth).map
      (fun sample => (sample.1, simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2)) =
      (P.binarySymmetric.experiment.transcriptLaw ν (simulatorLocalTest P fee hfee source hm stage) truth).map
        (fun record => (record.1, some (simulatorDrawDecoder P fee hfee source stage record))) := by
  have hd : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.StoppedWord =>
      (record.1, some (simulatorDrawDecoder P fee hfee source stage record))) :=
    measurable_fst.prodMk ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp
      (measurable_simulatorDrawDecoder P fee hfee source hm stage))
  rw [PaperProofs.Statistics.BinaryExperiment.transcriptLaw,
    Measure.map_map hd (P.binarySymmetric.experiment.measurable_stoppedTranscript _)]
  apply Measure.map_congr
  filter_upwards [P.binarySymmetric.experiment.expectedSamples_finite_stop ν
    (simulatorLocalTest P fee hfee source hm stage) truth hf] with sample hs
  exact Prod.ext rfl (simulatorDrawAt_eq_decoder_of_finite P fee hfee source hm stage sample hs)

/-- Pure auxiliary-tape sampling realizes the complete draw law, while
preserving the original source seed and virtual entry history jointly. -/
theorem simulatorDrawAt_auxiliaryTape_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    (ν.prod (auxiliaryTapeLaw P)).map
      (fun sample => (sample.1, simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2)) =
      (simulatorDrawLaw P fee hfee source hm stage ν).map (fun record => (record.1, some record.2)) := by
  have hs : Measurable (fun sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
      (sample.1, simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2)) :=
    measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)
  have hd : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      (record.1, some record.2)) := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp measurable_snd)
  have hg := measurable_simulatorDrawPair P fee hfee source hm stage
  rw [prod_auxiliaryTapeLaw, Measure.map_add _ _ hs, Measure.map_smul _ hs.aemeasurable, Measure.map_smul _ hs.aemeasurable,
    simulatorDrawAt_conditionalLaw P fee hfee source hm stage ν false (hf false),
    simulatorDrawAt_conditionalLaw P fee hfee source hm stage ν true (hf true)]
  unfold simulatorDrawLaw PaperProofs.Statistics.BinarySymmetric.Parameters.bayesStoppedLaw
  rw [Measure.map_add _ _ hg, Measure.map_smul _ hg.aemeasurable, Measure.map_smul _ hg.aemeasurable,
    Measure.map_add _ _ hd, Measure.map_smul _ hd.aemeasurable, Measure.map_smul _ hd.aemeasurable,
    Measure.map_map hd hg, Measure.map_map hd hg]
  rfl

end
end PDROC

