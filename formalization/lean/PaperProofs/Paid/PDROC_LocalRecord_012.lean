module
public import PaperProofs.Paid.PDROC_LocalRecord_008
public import PaperProofs.Statistics.PDROC_Lower_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Paid
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Statistics.BinarySymmetric

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Exact charge disintegration over the REAL stopped-word integer level.
It applies to every randomized non-MAP admissible rule after finite ET has
been established from its actual charge; no local performance oracle enters. -/
theorem bayesObservationCharge_eq_mean_endpointCharge
    (P : PaperProofs.Statistics.BinarySymmetric.Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) (hf : ∀ truth, P.experiment.expectedSamples ν test truth ≠ ⊤) :
    P.experiment.bayesObservationCharge ν test =
      ∫⁻ record : Seed × P.experiment.StoppedWord,
        ENNReal.ofReal (P.endpointCharge (wordSignedScore P record.2).natAbs : ℝ) ∂P.bayesStoppedLaw ν test := by
  rw [P.bayesObservationCharge_eq_posteriorInformation ν test hf,
    P.expectedPosteriorInformation_eq_stoppedLaw ν test hf]
  simp_rw [P.endpointChargeENN_eq_information, ← wordPosteriorError_eq_endpoint]
  have hm : Measurable (fun record : Seed × P.experiment.StoppedWord => phi (P.wordPosteriorError record.2)) :=
    (measurable_of_countable (fun word => phi (P.wordPosteriorError word))).comp measurable_snd
  exact (lintegral_const_mul _ hm).symm

/-- The original source record's observed integer score gives exactly Cm
on average, rather than merely a logarithmic information lower bound. -/
theorem sourceEntryFiniteRecordLaw_endpointCharge_mean
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (sourceEntryTest P fee hfee first accounting rule hm) truth ≠ ⊤) :
    P.binarySymmetric.experiment.bayesObservationCharge ν
      (sourceEntryTest P fee hfee first accounting rule hm) =
      ∫⁻ record : (Seed × Startup P.sharedInstance) × AuxiliaryRecord,
        ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.level : ℝ)
          ∂sourceEntryFiniteRecordLaw P fee hfee first accounting rule hm ν := by
  rw [P.binarySymmetric.bayesObservationCharge_eq_posteriorInformation ν _ hf,
    P.binarySymmetric.expectedPosteriorInformation_eq_stoppedLaw ν _ hf,
    sourceEntryFiniteRecordLaw]
  have hCm : Measurable (fun record : (Seed × Startup P.sharedInstance) × AuxiliaryRecord =>
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.level : ℝ)) :=
    (measurable_of_countable (fun record : AuxiliaryRecord =>
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ))).comp measurable_snd
  rw [lintegral_map hCm (measurable_sourceEntryRecordPair P fee hfee first accounting rule hm)]
  have hp (record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord) :
      ENNReal.ofReal (P.binarySymmetric.endpointCharge
        ((sourceEntryRecordPair P fee hfee first accounting rule) record).2.level : ℝ) =
        ENNReal.ofReal P.binarySymmetric.a * phi (P.binarySymmetric.wordPosteriorError record.2) := by
    rw [P.binarySymmetric.endpointChargeENN_eq_information]
    change ENNReal.ofReal P.binarySymmetric.a * phi
      (P.recordPosteriorError ((sourceEntryRecordPair P fee hfee first accounting rule) record).2) = _
    rw [← auxiliaryPosteriorLevels P ((sourceEntryRecordPair P fee hfee first accounting rule) record).2]
    change ENNReal.ofReal P.binarySymmetric.a * phi (P.binarySymmetric.wordPosteriorError
      (auxiliaryRecordWord P (sourceEntryRecordDecoder P fee hfee first accounting rule record))) = _
    rw [sourceEntryRecordDecoder_word]
  simp_rw [hp]
  have hPhi : Measurable (fun record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord =>
      phi (P.binarySymmetric.wordPosteriorError record.2)) :=
    (measurable_of_countable (fun word => phi (P.binarySymmetric.wordPosteriorError word))).comp measurable_snd
  exact (lintegral_const_mul _ hPhi).symm

end
end PDROC


