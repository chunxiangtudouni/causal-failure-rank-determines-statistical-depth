module

public import PaperProofs.Paid.PDROC_SimulatorLaw_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u} [MeasurableSpace Seed]

def reportedDrawSome (record : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool) :
    ((Seed × List (VisibleEvent I)) × Option (SimulatorDraw I)) × Bool :=
  ((record.1.1, some record.1.2), record.2)

theorem measurable_reportedDrawSome : Measurable (reportedDrawSome (I := I) (Seed := Seed)) :=
  ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_of_countable (some : SimulatorDraw I → Option (SimulatorDraw I))).comp
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd

noncomputable def simulatorSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × P.binarySymmetric.experiment.Tape)) :
    ((Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance)) × Bool :=
  coupledRecordTruth P (fun record => simulatorDrawRecord record.2) actualTruth
    ((sample.1.1, simulatorDrawAt P fee hfee source stage sample.1.1.1 sample.1.1.2 sample.1.2), sample.2)

set_option maxHeartbeats 800000 in
theorem measurable_simulatorSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (simulatorSampledReportedDraw P fee hfee source stage actualTruth) := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      Option (SimulatorDraw P.sharedInstance) => simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  have hc := measurable_coupledRecordTruth P
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) hr actualTruth
  exact hc.comp ((measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)).prodMap measurable_id)

set_option maxHeartbeats 800000 in
theorem simulatorSampledReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((ν.prod (auxiliaryTapeLaw P)).prod
      (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)).map
        (simulatorSampledReportedDraw P fee hfee source stage actualTruth) =
      (simulatorSourceReportedDrawLaw P fee hfee source hm stage ν).map reportedDrawSome := by
  let sampleDraw := fun sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
    (sample.1, simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2)
  let embed := fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
    (record.1, some record.2)
  let endpoint := P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth
  let couple := coupledRecordTruth P
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) actualTruth
  have hs : Measurable sampleDraw := measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)
  have he : Measurable embed := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp measurable_snd)
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
      simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  have hc : Measurable couple := measurable_coupledRecordTruth P _ hr actualTruth
  have hr' : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  have hc' := measurable_coupledRecordTruth P
    (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance => record.2.record)
      hr' actualTruth
  have hfirst := Measure.map_prod_map (ν.prod (auxiliaryTapeLaw P)) endpoint hs
    (measurable_id : Measurable (id : Bool × P.binarySymmetric.experiment.Tape → _))
  rw [Measure.map_id] at hfirst
  have hsecond := Measure.map_prod_map (simulatorDrawLaw P fee hfee source hm stage ν) endpoint he
    (measurable_id : Measurable (id : Bool × P.binarySymmetric.experiment.Tape → _))
  rw [Measure.map_id] at hsecond
  have hdraw : (ν.prod (auxiliaryTapeLaw P)).map sampleDraw =
      (simulatorDrawLaw P fee hfee source hm stage ν).map embed :=
    simulatorDrawAt_auxiliaryTape_law P fee hfee source hm stage ν hf
  calc
    _ = (((ν.prod (auxiliaryTapeLaw P)).map sampleDraw).prod endpoint).map couple :=
      (Measure.map_map hc (hs.prodMap measurable_id)).symm.trans (congrArg (fun μ => μ.map couple) hfirst.symm)
    _ = (((simulatorDrawLaw P fee hfee source hm stage ν).map embed).prod endpoint).map couple := by rw [hdraw]
    _ = (((simulatorDrawLaw P fee hfee source hm stage ν).prod endpoint).map
        (coupledRecordTruth P (fun record => record.2.record) actualTruth)).map reportedDrawSome := by
      rw [hsecond, Measure.map_map hc (he.prodMap measurable_id),
        Measure.map_map measurable_reportedDrawSome hc']
      rfl
    _ = _ := by rw [simulatorDraw_reportCouplingLaw P fee hfee source hm stage ν hf actualTruth]

noncomputable def simulatorMixedSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape))) :=
  simulatorSampledReportedDraw P fee hfee source stage sample.2.2.1
    (sample.1, (sample.2.1, sample.2.2.2))

theorem measurable_simulatorMixedSampledReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorMixedSampledReportedDraw P fee hfee source stage) := by
  let build := fun pair : (((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × P.experiment.Tape)) × Bool => simulatorSampledReportedDraw P fee hfee source stage pair.2 pair.1
  have hb : Measurable build := measurable_from_prod_countable_left
    (fun truth => measurable_simulatorSampledReportedDraw P fee hfee source hm stage truth)
  exact hb.comp ((measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_snd.comp measurable_snd).comp measurable_snd))).prodMk
      ((measurable_fst.comp measurable_snd).comp measurable_snd))

theorem simulatorMixedSampledReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    ((ν.prod (auxiliaryTapeLaw P)).prod (simulatorEndpointLaw P fee hfee stage)).map
      (simulatorMixedSampledReportedDraw P fee hfee source stage) =
      (simulatorSourceReportedDrawLaw P fee hfee source hm stage ν).map reportedDrawSome := by
  have hρ : SFinite (ν.prod (auxiliaryTapeLaw P) :
      Measure ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape)) := by
    change SFinite (ν.prod (auxiliaryTapeLaw P) :
      Measure ((Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape))
    infer_instance
  apply @prod_simulatorEndpointLaw_map_of_conditional_constant _ _ _ _ P fee hfee stage _ hρ
    (simulatorMixedSampledReportedDraw P fee hfee source stage)
    (measurable_simulatorMixedSampledReportedDraw P fee hfee source hm stage)
  intro truth
  exact simulatorSampledReportedDraw_law P fee hfee source hm stage ν hf truth

def optionalSourceDrawGuardGood (source : PolicyRule I Seed) (stage : I.Stage)
    (record : ((Seed × List (VisibleEvent I)) × Option (SimulatorDraw I)) × Bool) : Prop :=
  ∃ draw, record.1.2 = some draw ∧ sourceDrawGuardGood source stage ((record.1.1, draw), record.2)

theorem measurableSet_optionalSourceDrawGuardGood (source : PolicyRule I Seed)
    (hm : MeasurableRule source) (stage : I.Stage) :
    MeasurableSet {record | optionalSourceDrawGuardGood source stage record} := by
  have each (draw : SimulatorDraw I) : MeasurableSet
      {record : ((Seed × List (VisibleEvent I)) × Option (SimulatorDraw I)) × Bool |
        record.1.2 = some draw ∧ sourceDrawGuardGood source stage ((record.1.1, draw), record.2)} :=
    (((measurable_snd.comp measurable_fst) (measurableSet_singleton (some draw))).inter
      ((measurableSet_sourceDrawGuardGood source hm stage).preimage
        (((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd)))
  simpa only [optionalSourceDrawGuardGood, Set.ofPred_exists] using MeasurableSet.iUnion each

noncomputable def simulatorEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :=
  simulatorMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source) stage
    (simulatorEventualStageSample P fee hfee C accounting source stage sample)

theorem measurable_simulatorEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorEventualReportedDraw P fee hfee C accounting source stage) :=
  (measurable_simulatorMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source)
    (measurable_sourceForOptionalHistory source hm) stage).comp
      (measurable_simulatorEventualStageSample P fee hfee C accounting source hm stage)

theorem simulatorEventualReportedDraw_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEventualReportedDraw P fee hfee C accounting source.rule stage) =
      (simulatorSourceReportedDrawLaw P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)).map reportedDrawSome := by
  have hm := measurable_simulatorMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
  calc
    _ = (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorEventualStageSample P fee hfee C accounting source.rule stage)).map
          (simulatorMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source.rule) stage) :=
      (Measure.map_map hm (measurable_simulatorEventualStageSample P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = _ := by
      rw [simulatorEventualStageSample_law_of_entryLaw P fee hfee C accounting source ν stage hentry]
      exact simulatorMixedSampledReportedDraw_law P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage _
          (sourceEventualDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage hfinite)

/-- This is the concrete actual-sample guard witness used by finite-stage
flow. Its sole entry hypothesis is eliminated by stage induction. -/
theorem simulatorEventualReportedDraw_guardGood_ae_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      optionalSourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
        (simulatorEventualReportedDraw P fee hfee C accounting source.rule stage sample) := by
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  have hsource := sourceEventualReportedDraw_guardGood_ae P fee hfee C accounting source ν stage hfinite
  have hgood : ∀ᵐ record ∂(simulatorSourceReportedDrawLaw P fee hfee wrapped hm stage
      (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)).map reportedDrawSome,
      optionalSourceDrawGuardGood wrapped stage record := by
    apply (ae_map_iff measurable_reportedDrawSome.aemeasurable
      (measurableSet_optionalSourceDrawGuardGood wrapped hm stage)).mpr
    filter_upwards [hsource] with record hg
    exact ⟨record.1.2, rfl, hg⟩
  have hactual : ∀ᵐ record ∂((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEventualReportedDraw P fee hfee C accounting source.rule stage),
      optionalSourceDrawGuardGood wrapped stage record := by
    rw [simulatorEventualReportedDraw_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    exact hgood
  exact ae_of_ae_map
    (measurable_simulatorEventualReportedDraw P fee hfee C accounting source.rule source.measurable_rule stage).aemeasurable hactual

end PDROC
