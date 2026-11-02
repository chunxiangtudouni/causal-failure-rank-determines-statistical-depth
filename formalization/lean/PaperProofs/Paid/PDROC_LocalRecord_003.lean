module
public import PaperProofs.Paid.PDROC_LocalRecord_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u

/-- An independent auxiliary observation tape, sampled directly from its
fair mixture law. There is no latent or future truth coordinate in this seed. -/
noncomputable def auxiliaryTapeLaw (P : Parameters) : Measure P.binarySymmetric.experiment.Tape :=
  (1 / 2 : ℝ≥0∞) • P.binarySymmetric.experiment.tapeLaw false +
    (1 / 2 : ℝ≥0∞) • P.binarySymmetric.experiment.tapeLaw true

instance auxiliaryTapeLaw_probability (P : Parameters) : IsProbabilityMeasure (auxiliaryTapeLaw P) := by
  constructor
  simpa only [auxiliaryTapeLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one, one_div] using ENNReal.inv_two_add_inv_two

section
variable {Source : Type u} [MeasurableSpace Source]

theorem prod_auxiliaryTapeLaw (P : Parameters) (ν : Measure Source) [SFinite ν] :
    ν.prod (auxiliaryTapeLaw P) =
      (1 / 2 : ℝ≥0∞) • P.binarySymmetric.experiment.conditionalLaw ν false +
        (1 / 2 : ℝ≥0∞) • P.binarySymmetric.experiment.conditionalLaw ν true := by
  rw [auxiliaryTapeLaw, Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right]
  rfl

/-- The true fair stopped transcript law is obtained by sampling only the
original independent source seed and one auxiliary observation tape. -/
theorem bayesStoppedLaw_eq_auxiliaryTape_map (P : Parameters) (ν : Measure Source) [SFinite ν]
    (test : P.binarySymmetric.experiment.AdmissibleRule Source) :
    P.binarySymmetric.bayesStoppedLaw ν test =
      (ν.prod (auxiliaryTapeLaw P)).map (P.binarySymmetric.experiment.stoppedTranscript test) := by
  rw [prod_auxiliaryTapeLaw, Measure.map_add _ _ (P.binarySymmetric.experiment.measurable_stoppedTranscript test),
    Measure.map_smul _ (P.binarySymmetric.experiment.measurable_stoppedTranscript test).aemeasurable,
    Measure.map_smul _ (P.binarySymmetric.experiment.measurable_stoppedTranscript test).aemeasurable]
  rfl

end
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Exact pure-tape implementation of the finite source record kernel.
The original source seed and full public entry cache are both preserved. -/
theorem sourceEntryFiniteRecordLaw_eq_auxiliaryTape (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) [SFinite ν] :
    sourceEntryFiniteRecordLaw P fee hfee first accounting rule hm ν =
      (ν.prod (auxiliaryTapeLaw P)).map
        (fun sample => sourceEntryRecordPair P fee hfee first accounting rule
          (P.binarySymmetric.experiment.stoppedTranscript
            (sourceEntryTest P fee hfee first accounting rule hm) sample)) := by
  rw [sourceEntryFiniteRecordLaw, bayesStoppedLaw_eq_auxiliaryTape_map,
    Measure.map_map (measurable_sourceEntryRecordPair P fee hfee first accounting rule hm)
      (P.binarySymmetric.experiment.measurable_stoppedTranscript _)]
  rfl

/-- Sampling the full actual Option record on a pure auxiliary tape has
exactly the some-image of the finite record law, after finite local ET has
proved nonreturn null. Infinite observation charges were never discarded. -/
theorem sourceEntrySampleRecord_auxiliaryTape_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) [SFinite ν]
    (hf : ∀ x, P.binarySymmetric.experiment.expectedSamples ν
      (sourceEntryTest P fee hfee first accounting rule hm) x ≠ ⊤) :
    (ν.prod (auxiliaryTapeLaw P)).map
      (fun sample => (sample.1, sampleSourceEntryRecord P fee hfee first accounting rule hm sample)) =
      (sourceEntryFiniteRecordLaw P fee hfee first accounting rule hm ν).map
        (fun record => (record.1, some record.2)) := by
  have hs : Measurable (fun sample : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.Tape =>
      (sample.1, sampleSourceEntryRecord P fee hfee first accounting rule hm sample)) :=
    measurable_fst.prodMk (measurable_sampleSourceEntryRecord P fee hfee first accounting rule hm)
  have hd : Measurable (fun record : (Seed × Startup P.sharedInstance) × AuxiliaryRecord =>
      (record.1, some record.2)) := measurable_fst.prodMk
    ((measurable_of_countable (some : AuxiliaryRecord → Option AuxiliaryRecord)).comp measurable_snd)
  have hg := measurable_sourceEntryRecordPair P fee hfee first accounting rule hm
  rw [prod_auxiliaryTapeLaw, Measure.map_add _ _ hs,
    Measure.map_smul _ hs.aemeasurable, Measure.map_smul _ hs.aemeasurable,
    sourceEntrySampleRecord_law P fee hfee first accounting rule hm ν false (hf false),
    sourceEntrySampleRecord_law P fee hfee first accounting rule hm ν true (hf true)]
  unfold sourceEntryFiniteRecordLaw PaperProofs.Statistics.BinarySymmetric.Parameters.bayesStoppedLaw
  rw [Measure.map_add _ _ hg, Measure.map_smul _ hg.aemeasurable, Measure.map_smul _ hg.aemeasurable,
    Measure.map_add _ _ hd, Measure.map_smul _ hd.aemeasurable, Measure.map_smul _ hd.aemeasurable,
    Measure.map_map hd hg, Measure.map_map hd hg]
  rfl

end
end PDROC

