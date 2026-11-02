module
public import PaperProofs.Paid.PDROC_LocalRecord_017
public import PaperProofs.Paid.PDROC_RecordCoupling_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

instance simulatorDrawLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (simulatorDrawLaw P fee hfee source hm stage ν) := by
  unfold simulatorDrawLaw
  infer_instance

/-- Independently the ORIGINAL local source's joint reported-truth/draw
law, with its whole original seed and virtual entry history retained. -/
noncomputable def simulatorSourceReportedDrawLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) :
    Measure (((Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance) × Bool) :=
  (1 / 2 : ℝ≥0∞) •
    ((P.binarySymmetric.experiment.transcriptLaw ν (simulatorLocalTest P fee hfee source hm stage) false).map
      (simulatorDrawPair P fee hfee source stage)).map (fun record => (record, false)) +
  (1 / 2 : ℝ≥0∞) •
    ((P.binarySymmetric.experiment.transcriptLaw ν (simulatorLocalTest P fee hfee source hm stage) true).map
      (simulatorDrawPair P fee hfee source stage)).map (fun record => (record, true))

/-- For EITHER real truth, the actual record-indexed integer-boundary test
and post-report coordinate flip produce exactly the ORIGINAL source joint
reported-truth/draw law. The old private seed and full virtual entry history
are preserved jointly, rather than only scalar error probabilities. -/
theorem simulatorDraw_reportCouplingLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤)
    (actualTruth : Bool) :
    ((simulatorDrawLaw P fee hfee source hm stage ν).prod
      (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)).map
        (coupledRecordTruth P (fun record => record.2.record) actualTruth) =
      simulatorSourceReportedDrawLaw P fee hfee source hm stage ν := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      record.2.record) := (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  rw [coupledRecordTruth_jointLaw P (fun record => record.2.record) hr
    (simulatorDrawLaw P fee hfee source hm stage ν) actualTruth]
  unfold posteriorRecordLaw simulatorSourceReportedDrawLaw
  change ((simulatorDrawLaw P fee hfee source hm stage ν).withDensity
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass false (auxiliaryRecordWord P record.2.record)))).map
        (fun record => (record, false)) +
    ((simulatorDrawLaw P fee hfee source hm stage ν).withDensity
      (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass true (auxiliaryRecordWord P record.2.record)))).map
        (fun record => (record, true)) = _
  rw [simulatorDrawLaw_posterior P fee hfee source hm stage ν hf false,
    simulatorDrawLaw_posterior P fee hfee source hm stage ν hf true]
  have hfalse : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      (record, false)) := measurable_id.prodMk measurable_const
  have htrue : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      (record, true)) := measurable_id.prodMk measurable_const
  rw [Measure.map_smul (1 / 2 : ℝ≥0∞) hfalse.aemeasurable,
    Measure.map_smul (1 / 2 : ℝ≥0∞) htrue.aemeasurable]

end
end PDROC


