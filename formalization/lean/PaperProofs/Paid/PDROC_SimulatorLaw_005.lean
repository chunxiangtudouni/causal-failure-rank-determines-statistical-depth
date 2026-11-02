module

public import PaperProofs.Paid.PDROC_SimulatorLaw_003
public import PaperProofs.Paid.PDROC_LocalRecord_019

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- The complete source packet at its first non-review action. The write
serial counts actual actions, not events; a write and its early report
therefore share the same serial. Stop and abandonment remain distinct. -/
def sourceDrawTerminalHistory (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) : List (VisibleEvent I) :=
  let before := entry ++ simulatorReviewPacket stage draw.record
  let serial := (historyActions entry).length + draw.record.observations.length
  match draw.action with
  | .write current bit => before ++ [.wrote current bit serial, .report current truth serial]
  | .stop => before ++ [.stopped]
  | _ => before ++ [.abandoned]

/-- A full stage, including its genuine allocation/execution/exit actions.
The finite postwrite transducer freezes as soon as that stage is left. -/
def sourceDrawStageExit (source : PolicyRule I Seed) (stage : I.Stage)
    (sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool) :
    Seed × List (VisibleEvent I) :=
  (sample.1.1.1, postwriteStageTrace source sample.1.1.1 stage
    (sourceDrawTerminalHistory stage sample.1.1.2 sample.1.2 sample.2) 3)

set_option maxHeartbeats 800000 in
theorem measurable_sourceDrawStageExit [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (stage : I.Stage) :
    Measurable (sourceDrawStageExit source stage) := by
  have hs : Measurable (fun sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool =>
      sample.1.1.1) := (measurable_fst.comp measurable_fst).comp measurable_fst
  have hh : Measurable (fun sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool =>
      sourceDrawTerminalHistory stage sample.1.1.2 sample.1.2 sample.2) :=
    (measurable_of_countable (fun data : (List (VisibleEvent I) × SimulatorDraw I) × Bool =>
      sourceDrawTerminalHistory stage data.1.1 data.1.2 data.2)).comp
      ((((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  change Measurable (fun sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool =>
    (sample.1.1.1, postwriteStageTrace source sample.1.1.1 stage
      (sourceDrawTerminalHistory stage sample.1.1.2 sample.1.2 sample.2) 3))
  have htrace := (measurable_postwriteStageTrace source hm stage 3).comp (hs.prodMk hh)
  exact hs.prodMk htrace

theorem sourceDrawTerminalHistory_stop (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) (ha : draw.action = .stop) :
    sourceDrawTerminalHistory stage entry draw truth =
      entry ++ simulatorReviewPacket stage draw.record ++ [.stopped] := by
  simp only [sourceDrawTerminalHistory, ha]

theorem sourceDrawTerminalHistory_abandon (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) (ha : draw.action = .abandon) :
    sourceDrawTerminalHistory stage entry draw truth =
      entry ++ simulatorReviewPacket stage draw.record ++ [.abandoned] := by
  simp only [sourceDrawTerminalHistory, ha]

theorem sourceDrawTerminalHistory_write (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth bit : Bool) (ha : draw.action = .write stage bit) :
    sourceDrawTerminalHistory stage entry draw truth =
      entry ++ simulatorReviewPacket stage draw.record ++
        [.wrote stage bit ((historyActions entry).length + draw.record.observations.length),
          .report stage truth ((historyActions entry).length + draw.record.observations.length)] := by
  simp only [sourceDrawTerminalHistory, ha]

section Laws

variable [MeasurableSpace Seed]

/-- The original direct source test, followed by the source's own complete
postwrite controller. This definition samples no simulator endpoint. -/
noncomputable def sourceDirectStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (truth : Bool)
    (sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape) :
    Seed × List (VisibleEvent P.sharedInstance) :=
  sourceDrawStageExit source stage
    (simulatorDrawPair P fee hfee source stage
      (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee source hm stage) sample), truth)

theorem measurable_sourceDirectStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (truth : Bool) :
    Measurable (sourceDirectStageExit P fee hfee source hm stage truth) :=
  (measurable_sourceDrawStageExit source hm stage).comp
    (((measurable_simulatorDrawPair P fee hfee source hm stage).comp
      (P.binarySymmetric.experiment.measurable_stoppedTranscript _)).prodMk measurable_const)

/-- An independently defined original source-stage kernel. Both branches
sample the original conditional tape and the original source action. -/
noncomputable def sourceDirectStageExitLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) :
    Measure (Seed × List (VisibleEvent P.sharedInstance)) :=
  (1 / 2 : ℝ≥0∞) • ((P.binarySymmetric.experiment.conditionalLaw ν false).map
    (sourceDirectStageExit P fee hfee source hm stage false)) +
  (1 / 2 : ℝ≥0∞) • ((P.binarySymmetric.experiment.conditionalLaw ν true).map
    (sourceDirectStageExit P fee hfee source hm stage true))

theorem simulatorSourceReportedDrawLaw_stageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) :
    (simulatorSourceReportedDrawLaw P fee hfee source hm stage ν).map
      (sourceDrawStageExit source stage) = sourceDirectStageExitLaw P fee hfee source hm stage ν := by
  have he := measurable_sourceDrawStageExit source hm stage
  have hd := measurable_simulatorDrawPair P fee hfee source hm stage
  have hf : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      (record, false)) := measurable_id.prodMk measurable_const
  have ht : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
      (record, true)) := measurable_id.prodMk measurable_const
  unfold simulatorSourceReportedDrawLaw sourceDirectStageExitLaw
  rw [Measure.map_add _ _ he, Measure.map_smul _ he.aemeasurable, Measure.map_smul _ he.aemeasurable,
    Measure.map_map he hf, Measure.map_map he ht,
    Measure.map_map (he.comp hf) hd, Measure.map_map (he.comp ht) hd]
  unfold PaperProofs.Statistics.BinaryExperiment.transcriptLaw
  rw [Measure.map_map ((he.comp hf).comp hd) (P.binarySymmetric.experiment.measurable_stoppedTranscript _),
    Measure.map_map ((he.comp ht).comp hd) (P.binarySymmetric.experiment.measurable_stoppedTranscript _)]
  rfl

set_option maxHeartbeats 800000 in
/-- Exact full-stage transport for either actual truth. The conclusion
retains the old private seed and the entire source exit history, including
allocation, execution, stop, abandonment, and the source's original serials. -/
theorem simulatorDraw_stageExitCouplingLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((simulatorDrawLaw P fee hfee source hm stage ν).prod
      (P.binarySymmetric.experiment.conditionalLaw
        PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw actualTruth)).map
      (fun sample => sourceDrawStageExit source stage
        (coupledRecordTruth P (fun record => record.2.record) actualTruth sample)) =
      sourceDirectStageExitLaw P fee hfee source hm stage ν := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  calc
    _ = (((simulatorDrawLaw P fee hfee source hm stage ν).prod
        (P.binarySymmetric.experiment.conditionalLaw
          PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw actualTruth)).map
          (coupledRecordTruth P (fun record => record.2.record) actualTruth)).map
            (sourceDrawStageExit source stage) :=
      (Measure.map_map (measurable_sourceDrawStageExit source hm stage)
        (measurable_coupledRecordTruth P (fun record => record.2.record) hr actualTruth)).symm
    _ = (simulatorSourceReportedDrawLaw P fee hfee source hm stage ν).map
        (sourceDrawStageExit source stage) := by
      rw [simulatorDraw_reportCouplingLaw P fee hfee source hm stage ν hf actualTruth]
    _ = _ := simulatorSourceReportedDrawLaw_stageExit P fee hfee source hm stage ν

end Laws
end PDROC
