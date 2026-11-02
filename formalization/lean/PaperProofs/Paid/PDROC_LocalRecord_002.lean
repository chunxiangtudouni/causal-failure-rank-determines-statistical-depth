module
public import PaperProofs.Paid.PDROC_LocalRecord_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u v

/-- Push a density through a measurable map when that density is computed
from the mapped record itself. -/
theorem map_withDensity_comp {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (g : A → B) (hg : Measurable g) (f : B → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun a => f (g a))).map g = (μ.map g).withDensity f := by
  ext S hS
  rw [Measure.map_apply hg hS, withDensity_apply _ (hg hS), withDensity_apply _ hS,
    ← lintegral_indicator (hg hS), ← lintegral_indicator hS,
    lintegral_map (hf.indicator hS) hg]
  apply lintegral_congr
  intro a
  by_cases ha : g a ∈ S <;> simp [ha]

noncomputable def auxiliaryRecordWord (P : Parameters) (record : AuxiliaryRecord) :
    P.binarySymmetric.experiment.StoppedWord :=
  ⟨record.observations.length, fun k => record.observations[k.val]⟩

section
variable {Seed : Type u} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem sourceEntryRecordDecoder_word (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed)
    (record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord) :
    auxiliaryRecordWord P (sourceEntryRecordDecoder P fee hfee first accounting rule record) = record.2 := by
  rcases record with ⟨source, ⟨n, word⟩⟩
  change (⟨(List.ofFn word).length, (List.ofFn word).get⟩ :
    Σ n, Fin n → Fin P.binarySymmetric.experiment.alphabetSize) = ⟨n, word⟩
  exact List.equivSigmaTuple.right_inv ⟨n, word⟩

noncomputable def sourceEntryRecordPair (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed)
    (record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord) :
    (Seed × Startup P.sharedInstance) × AuxiliaryRecord :=
  (record.1, sourceEntryRecordDecoder P fee hfee first accounting rule record)

theorem measurable_sourceEntryRecordPair (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    Measurable (sourceEntryRecordPair P fee hfee first accounting rule) :=
  measurable_fst.prodMk (measurable_sourceEntryRecordDecoder P fee hfee first accounting rule hm)

/-- The auxiliary record law is the image of the TRUE stopped transcript
law. Its posterior identity below is proved, not included as a record field. -/
noncomputable def sourceEntryFiniteRecordLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) :
    Measure ((Seed × Startup P.sharedInstance) × AuxiliaryRecord) :=
  (P.binarySymmetric.bayesStoppedLaw ν (sourceEntryTest P fee hfee first accounting rule hm)).map
    (sourceEntryRecordPair P fee hfee first accounting rule)

/-- Exact original-source/record posterior density. Finite ET is used only
for this D03 identity; the sampler and its admissible test have no such
input restriction. No future truth is included in the source coordinate. -/
theorem sourceEntryFiniteRecordLaw_posterior (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) [IsProbabilityMeasure ν]
    (hf : ∀ x, P.binarySymmetric.experiment.expectedSamples ν
      (sourceEntryTest P fee hfee first accounting rule hm) x ≠ ⊤) (truth : Bool) :
    (sourceEntryFiniteRecordLaw P fee hfee first accounting rule hm ν).withDensity
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P record.2))) =
      (1 / 2 : ℝ≥0∞) •
        (P.binarySymmetric.experiment.transcriptLaw ν (sourceEntryTest P fee hfee first accounting rule hm) truth).map
          (sourceEntryRecordPair P fee hfee first accounting rule) := by
  have hg := measurable_sourceEntryRecordPair P fee hfee first accounting rule hm
  have hd : Measurable (fun record : (Seed × Startup P.sharedInstance) × AuxiliaryRecord =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P record.2))) :=
    (measurable_of_countable (fun record : AuxiliaryRecord =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth (auxiliaryRecordWord P record)))).comp measurable_snd
  have h := map_withDensity_comp
    (P.binarySymmetric.bayesStoppedLaw ν (sourceEntryTest P fee hfee first accounting rule hm))
    (sourceEntryRecordPair P fee hfee first accounting rule) hg _ hd
  have hid : (fun record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth
        (auxiliaryRecordWord P ((sourceEntryRecordPair P fee hfee first accounting rule) record).2))) =
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth record.2)) := by
    funext record
    rw [sourceEntryRecordPair, sourceEntryRecordDecoder_word]
  rw [hid, P.binarySymmetric.bayesStoppedLaw_posterior_withDensity ν _ hf truth,
    Measure.map_smul (1 / 2 : ℝ≥0∞) hg.aemeasurable] at h
  exact h.symm

/-- For finite local charge the finite-record law is precisely the law of
the actual record sampler (with outer some); the nonreturn branch is proved
null rather than erased from the definition or its observation bill. -/
theorem sourceEntrySampleRecord_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) (truth : Bool)
    (hf : P.binarySymmetric.experiment.expectedSamples ν
      (sourceEntryTest P fee hfee first accounting rule hm) truth ≠ ⊤) :
    (P.binarySymmetric.experiment.conditionalLaw ν truth).map
      (fun sample => (sample.1, sampleSourceEntryRecord P fee hfee first accounting rule hm sample)) =
      (P.binarySymmetric.experiment.transcriptLaw ν
        (sourceEntryTest P fee hfee first accounting rule hm) truth).map
          (fun record => (record.1, some (sourceEntryRecordDecoder P fee hfee first accounting rule record))) := by
  have hdecoder : Measurable (fun record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord =>
      (record.1, some (sourceEntryRecordDecoder P fee hfee first accounting rule record))) :=
    measurable_fst.prodMk ((measurable_of_countable (some : AuxiliaryRecord → Option AuxiliaryRecord)).comp
      (measurable_sourceEntryRecordDecoder P fee hfee first accounting rule hm))
  rw [PaperProofs.Statistics.BinaryExperiment.transcriptLaw,
    Measure.map_map hdecoder (P.binarySymmetric.experiment.measurable_stoppedTranscript _)]
  apply Measure.map_congr
  filter_upwards [P.binarySymmetric.experiment.expectedSamples_finite_stop ν
    (sourceEntryTest P fee hfee first accounting rule hm) truth hf] with sample hs
  simp only [Function.comp_apply, sampleSourceEntryRecord, hs, ↓reduceIte]
  rfl

end
end PDROC


