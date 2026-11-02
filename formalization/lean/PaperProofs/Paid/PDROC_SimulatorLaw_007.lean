module

public import PaperProofs.Paid.PDROC_SimulatorLaw_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u} [MeasurableSpace Seed]

def sourceOptionalDrawStageExit (source : PolicyRule I Seed) (stage : I.Stage)
    (sample : ((Seed × List (VisibleEvent I)) × Option (SimulatorDraw I)) × Bool) :
    Seed × EntryHistory I :=
  (sample.1.1.1, sample.1.2.map (fun draw => (sourceDrawStageExit source stage ((sample.1.1, draw), sample.2)).2))

theorem measurable_sourceOptionalDrawStageExit (source : PolicyRule I Seed)
    (hm : MeasurableRule source) (stage : I.Stage) :
    Measurable (sourceOptionalDrawStageExit source stage) := by
  let build := fun pair : ((Seed × List (VisibleEvent I)) × Bool) × Option (SimulatorDraw I) =>
    (pair.1.1.1, pair.2.map (fun draw => (sourceDrawStageExit source stage ((pair.1.1, draw), pair.1.2)).2))
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro draw
    cases draw with
    | none => exact (measurable_fst.comp measurable_fst).prodMk measurable_const
    | some draw =>
      change Measurable (fun pair : (Seed × List (VisibleEvent I)) × Bool =>
        (pair.1.1, some (sourceDrawStageExit source stage ((pair.1, draw), pair.2)).2))
      have hi : Measurable (fun pair : (Seed × List (VisibleEvent I)) × Bool =>
          ((pair.1, draw), pair.2)) :=
        (measurable_fst.prodMk measurable_const).prodMk measurable_snd
      have hh := (measurable_snd.comp (measurable_sourceDrawStageExit source hm stage)).comp hi
      exact (measurable_fst.comp measurable_fst).prodMk
        ((measurable_of_countable (some : List (VisibleEvent I) → EntryHistory I)).comp hh)
  change Measurable (fun sample : ((Seed × List (VisibleEvent I)) × Option (SimulatorDraw I)) × Bool =>
    build ((sample.1.1, sample.2), sample.1.2))
  exact hb.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst))

/-- The actual report coordinate flip, retaining genuine no-draw as none. -/
noncomputable def simulatorOptionalStageExit (P : Parameters)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance)) ×
      (Bool × P.binarySymmetric.experiment.Tape)) : Seed × EntryHistory P.sharedInstance :=
  sourceOptionalDrawStageExit source stage
    (coupledRecordTruth P (fun record => simulatorDrawRecord record.2) actualTruth sample)

set_option maxHeartbeats 800000 in
theorem measurable_simulatorOptionalStageExit (P : Parameters)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (simulatorOptionalStageExit P source stage actualTruth) := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      Option (SimulatorDraw P.sharedInstance) => simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  have hc := measurable_coupledRecordTruth P (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
    Option (SimulatorDraw P.sharedInstance) => simulatorDrawRecord record.2) hr actualTruth
  have he := (measurable_sourceOptionalDrawStageExit source hm stage).comp hc
  exact he

/-- The simulator's actual auxiliary tape is sampled before its fresh
endpoint coin and tape. This map is the complete stage exit history. -/
noncomputable def simulatorSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × P.binarySymmetric.experiment.Tape)) : Seed × EntryHistory P.sharedInstance :=
  simulatorOptionalStageExit P source stage actualTruth
    ((sample.1.1, simulatorDrawAt P fee hfee source stage sample.1.1.1 sample.1.1.2 sample.1.2), sample.2)

theorem measurable_simulatorSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (simulatorSampledStageExit P fee hfee source stage actualTruth) :=
  (measurable_simulatorOptionalStageExit P source hm stage actualTruth).comp
    ((measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)).prodMap measurable_id)

set_option maxHeartbeats 800000 in
/-- Exact single-stage law for the REAL auxiliary-tape draw sampler and
the REAL independent endpoint experiment, for each actual truth. Its target
is the original source's conditional-tape/full-controller stage law. -/
theorem simulatorSampledStageExit_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((ν.prod (auxiliaryTapeLaw P)).prod
      (P.binarySymmetric.experiment.conditionalLaw
        PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw actualTruth)).map
          (simulatorSampledStageExit P fee hfee source stage actualTruth) =
      (sourceDirectStageExitLaw P fee hfee source hm stage ν).map (fun result => (result.1, some result.2)) := by
  let sampleDraw := fun sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
    (sample.1, simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2)
  let embed := fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
    (record.1, some record.2)
  let endpoint := P.binarySymmetric.experiment.conditionalLaw
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw actualTruth
  have hs : Measurable sampleDraw := measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)
  have he : Measurable embed := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp
      measurable_snd)
  have ho := measurable_simulatorOptionalStageExit P source hm stage actualTruth
  have hmSome : Measurable (fun result : Seed × List (VisibleEvent P.sharedInstance) =>
      (result.1, (some result.2 : EntryHistory P.sharedInstance))) :=
    measurable_fst.prodMk ((measurable_of_countable
      (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp measurable_snd)
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  have hc := (measurable_sourceDrawStageExit source hm stage).comp
    (measurable_coupledRecordTruth P (fun record => record.2.record) hr actualTruth)
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
    _ = (((ν.prod (auxiliaryTapeLaw P)).map sampleDraw).prod endpoint).map
        (simulatorOptionalStageExit P source stage actualTruth) := by
      exact (Measure.map_map ho (hs.prodMap measurable_id)).symm.trans (congrArg (fun μ => μ.map
        (simulatorOptionalStageExit P source stage actualTruth)) hfirst.symm)
    _ = (((simulatorDrawLaw P fee hfee source hm stage ν).map embed).prod endpoint).map
        (simulatorOptionalStageExit P source stage actualTruth) := by rw [hdraw]
    _ = ((simulatorDrawLaw P fee hfee source hm stage ν).prod endpoint).map
        (fun sample => let result := sourceDrawStageExit source stage (coupledRecordTruth P (fun record => record.2.record) actualTruth sample); (result.1, some result.2)) := by
      rw [hsecond, Measure.map_map ho (he.prodMap measurable_id)]
      rfl
    _ = (((simulatorDrawLaw P fee hfee source hm stage ν).prod endpoint).map
        (fun sample => sourceDrawStageExit source stage
          (coupledRecordTruth P (fun record => record.2.record) actualTruth sample))).map (fun result => (result.1, some result.2)) :=
      (Measure.map_map hmSome hc).symm
    _ = _ := by rw [simulatorDraw_stageExitCouplingLaw P fee hfee source hm stage ν hf actualTruth]

end PDROC

