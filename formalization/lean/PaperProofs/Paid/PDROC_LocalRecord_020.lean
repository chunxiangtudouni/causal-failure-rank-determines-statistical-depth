module
public import PaperProofs.Paid.PDROC_LocalRecord_019
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
variable {Source : Type u} [MeasurableSpace Source]

/-- The ACTUAL observation bill of the chosen integer-boundary test. The
fresh endpoint coin and current actual tape are separate from record source. -/
noncomputable def indexedRecordEndpointCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (pair : Source × (Bool × P.binarySymmetric.experiment.Tape)) : ℝ≥0∞ :=
  P.binarySymmetric.experiment.observationCharge
    ((P.binarySymmetric.rocEndpointTest (recordOf pair.1).level).rule.stop pair.2.1 pair.2.2)

theorem measurable_indexedRecordEndpointCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (hr : Measurable recordOf) : Measurable (indexedRecordEndpointCharge P recordOf) := by
  have hfamily : Measurable (fun pair : AuxiliaryRecord × (Bool × P.binarySymmetric.experiment.Tape) =>
      P.binarySymmetric.experiment.observationCharge
        ((P.binarySymmetric.rocEndpointTest pair.1.level).rule.stop pair.2.1 pair.2.2)) := by
    apply measurable_from_prod_countable_right
    intro record
    exact (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp
      (P.binarySymmetric.rocEndpointTest record.level).measurable_stop
  have hpair : Measurable (fun pair : Source × (Bool × P.binarySymmetric.experiment.Tape) => (recordOf pair.1, pair.2)) :=
    (hr.comp measurable_fst).prodMk measurable_snd
  have hm := hfamily.comp hpair
  exact hm

/-- Abandoning records buy no new actual observations. All original source
observations still remain in the separate source Cm mean accounting. -/
noncomputable def indexedRecordWritingCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (pair : Source × (Bool × P.binarySymmetric.experiment.Tape)) : ℝ≥0∞ :=
  if (recordOf pair.1).decision.isSome = true then indexedRecordEndpointCharge P recordOf pair else 0

theorem measurable_indexedRecordWritingCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (hr : Measurable recordOf) : Measurable (indexedRecordWritingCharge P recordOf) := by
  have hgate : MeasurableSet {pair : Source × (Bool × P.binarySymmetric.experiment.Tape) |
      (recordOf pair.1).decision.isSome = true} :=
    ((measurable_of_countable (fun record : AuxiliaryRecord => record.decision.isSome)).comp
      (hr.comp measurable_fst)) (measurableSet_singleton true)
  exact (measurable_indexedRecordEndpointCharge P recordOf hr).ite hgate measurable_const

/-- Exact record-indexed endpoint fee, separately under each real truth. -/
theorem lintegral_indexedRecordEndpointCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (hr : Measurable recordOf) (ρ : Measure Source) [SFinite ρ] (actualTruth : Bool) :
    (∫⁻ pair, indexedRecordEndpointCharge P recordOf pair
      ∂ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)) =
      ∫⁻ source, ENNReal.ofReal (P.binarySymmetric.endpointCharge (recordOf source).level : ℝ) ∂ρ := by
  rw [lintegral_prod _ (measurable_indexedRecordEndpointCharge P recordOf hr).aemeasurable]
  apply lintegral_congr
  intro source
  exact rocEndpointTest_expectedCharge P.binarySymmetric (recordOf source).level actualTruth

/-- Exact ACTUAL fee of writing-only replacement tests. -/
theorem lintegral_indexedRecordWritingCharge (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (hr : Measurable recordOf) (ρ : Measure Source) [SFinite ρ] (actualTruth : Bool) :
    (∫⁻ pair, indexedRecordWritingCharge P recordOf pair
      ∂ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)) =
      ∫⁻ source, if (recordOf source).decision.isSome = true
        then ENNReal.ofReal (P.binarySymmetric.endpointCharge (recordOf source).level : ℝ) else 0 ∂ρ := by
  rw [lintegral_prod _ (measurable_indexedRecordWritingCharge P recordOf hr).aemeasurable]
  apply lintegral_congr
  intro source
  by_cases hs : (recordOf source).decision.isSome = true
  · simp only [indexedRecordWritingCharge, hs, ↓reduceIte]
    exact rocEndpointTest_expectedCharge P.binarySymmetric (recordOf source).level actualTruth
  · simp only [indexedRecordWritingCharge, hs, Bool.false_eq_true, ↓reduceIte, lintegral_zero]

theorem lintegral_indexedRecordWritingCharge_le_endpointMean (P : Parameters) (recordOf : Source → AuxiliaryRecord)
    (hr : Measurable recordOf) (ρ : Measure Source) [SFinite ρ] (actualTruth : Bool) :
    (∫⁻ pair, indexedRecordWritingCharge P recordOf pair
      ∂ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)) ≤
      ∫⁻ source, ENNReal.ofReal (P.binarySymmetric.endpointCharge (recordOf source).level : ℝ) ∂ρ := by
  rw [lintegral_indexedRecordWritingCharge P recordOf hr ρ actualTruth]
  apply lintegral_mono
  intro source
  dsimp only
  split_ifs
  · exact le_rfl
  · exact zero_le


end
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Actual writing-only boundary replacement observes no more, in mean,
than the original arbitrary-decision local source test. -/
theorem simulatorDraw_writingCharge_le_sourceCharge (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤)
    (actualTruth : Bool) :
    (∫⁻ pair, indexedRecordWritingCharge P (fun record => record.2.record) pair
      ∂(simulatorDrawLaw P fee hfee source hm stage ν).prod
        (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)) ≤
      P.binarySymmetric.experiment.bayesObservationCharge ν (simulatorLocalTest P fee hfee source hm stage) := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  exact (lintegral_indexedRecordWritingCharge_le_endpointMean P _ hr
    (simulatorDrawLaw P fee hfee source hm stage ν) actualTruth).trans
      (simulatorDrawLaw_endpointCharge_mean P fee hfee source hm stage ν hf).symm.le

end
end PDROC



