module

public import PaperProofs.Paid.PDROC_OverlayKernel_008
public import PaperProofs.Paid.PDROC_SimulatorLaw_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def overlaySampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × P.experiment.Tape)) :
    ((Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance)) × Bool :=
  overlayCoupledRecordTruth P fee hfee (fun record => simulatorDrawRecord record.2) actualTruth
    ((sample.1.1, simulatorDrawAt P 0 (by norm_num) source stage sample.1.1.1 sample.1.1.2 sample.1.2), sample.2)

set_option maxHeartbeats 800000 in
theorem measurable_overlaySampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (overlaySampledReportedDraw P fee hfee source stage actualTruth) := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      Option (SimulatorDraw P.sharedInstance) => simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  have hc := measurable_overlayCoupledRecordTruth P fee hfee
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) hr actualTruth
  exact hc.comp ((measurable_fst.prodMk (measurable_simulatorDrawAt P 0 (by norm_num) source hm stage)).prodMap measurable_id)

set_option maxHeartbeats 800000 in
theorem overlaySampledReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((ν.prod (auxiliaryTapeLaw P)).prod
      (overlayRowConditionalLaw P fee hfee actualTruth)).map
        (overlaySampledReportedDraw P fee hfee source stage actualTruth) =
      (simulatorSourceReportedDrawLaw P 0 (by norm_num) source hm stage ν).map reportedDrawSome := by
  let sampleDraw := fun sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
    (sample.1, simulatorDrawAt P 0 (by norm_num) source stage sample.1.1 sample.1.2 sample.2)
  let embed := fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
    (record.1, some record.2)
  let endpoint := overlayRowConditionalLaw P fee hfee actualTruth
  let couple := overlayCoupledRecordTruth P fee hfee
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) actualTruth
  have hs : Measurable sampleDraw := measurable_fst.prodMk (measurable_simulatorDrawAt P 0 (by norm_num) source hm stage)
  have he : Measurable embed := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp measurable_snd)
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  have hc : Measurable couple := measurable_overlayCoupledRecordTruth P fee hfee _ hr actualTruth
  have hr' : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  have hc' := measurable_overlayCoupledRecordTruth P fee hfee
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance => record.2.record)
      hr' actualTruth
  have hfirst := Measure.map_prod_map (ν.prod (auxiliaryTapeLaw P)) endpoint hs
    (measurable_id : Measurable (id : OverlayStageCoins × P.experiment.Tape → _))
  rw [Measure.map_id] at hfirst
  have hsecond := Measure.map_prod_map (simulatorDrawLaw P 0 (by norm_num) source hm stage ν) endpoint he
    (measurable_id : Measurable (id : OverlayStageCoins × P.experiment.Tape → _))
  rw [Measure.map_id] at hsecond
  have hdraw : (ν.prod (auxiliaryTapeLaw P)).map sampleDraw =
      (simulatorDrawLaw P 0 (by norm_num) source hm stage ν).map embed :=
    simulatorDrawAt_auxiliaryTape_law P 0 (by norm_num) source hm stage ν hf
  calc
    _ = (((ν.prod (auxiliaryTapeLaw P)).map sampleDraw).prod endpoint).map couple :=
      (Measure.map_map hc (hs.prodMap measurable_id)).symm.trans (congrArg (fun μ => μ.map couple) hfirst.symm)
    _ = (((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).map embed).prod endpoint).map couple := by rw [hdraw]
    _ = (((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod endpoint).map
        (overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth)).map reportedDrawSome := by
      rw [hsecond, Measure.map_map hc (he.prodMap measurable_id),
        Measure.map_map measurable_reportedDrawSome hc']
      rfl
    _ = _ := by rw [overlayDraw_reportCouplingLaw P fee hfee source hm stage ν hf actualTruth]


noncomputable def overlayMixedSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × (Bool × P.experiment.Tape))) :=
  overlaySampledReportedDraw P fee hfee source stage sample.2.2.1
    (sample.1, (sample.2.1, sample.2.2.2))

set_option maxHeartbeats 800000 in
theorem measurable_overlayMixedSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayMixedSampledReportedDraw P fee hfee source stage) := by
  let build := fun pair : (((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × P.experiment.Tape)) × Bool =>
    overlaySampledReportedDraw P fee hfee source stage pair.2 pair.1
  have hb : Measurable build := measurable_from_prod_countable_left
    (fun truth => measurable_overlaySampledReportedDraw P fee hfee source hm stage truth)
  have hp : Measurable (fun sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × (Bool × P.experiment.Tape)) =>
      ((sample.1, (sample.2.1, sample.2.2.2)), sample.2.2.1)) :=
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_snd)
  exact hb.comp hp

/-- Keep the entire old seed, entry, auxiliary draw/action and reconstructed
reported truth. This is the law needed to transport pure source guard facts. -/
theorem overlayMixedSampledReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) :
    ((ν.prod (auxiliaryTapeLaw P)).prod
      ((overlayPaidStageCoinsLaw P fee hfee).prod ((P.input fee hfee).stageLaw stage))).map
        (overlayMixedSampledReportedDraw P fee hfee source stage) =
      (simulatorSourceReportedDrawLaw P 0 (by norm_num) source hm stage ν).map reportedDrawSome := by
  apply prod_overlayRowWorldLaw_map_of_conditional_constant P fee hfee stage
    (ν.prod (auxiliaryTapeLaw P)) (overlayPaidStageCoinsLaw P fee hfee)
    (overlayMixedSampledReportedDraw P fee hfee source stage)
    (measurable_overlayMixedSampledReportedDraw P fee hfee source hm stage)
  intro truth
  exact overlaySampledReportedDraw_law P fee hfee source hm stage ν hf truth

end PDROC
