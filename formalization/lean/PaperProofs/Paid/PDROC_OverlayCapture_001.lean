module

public import PaperProofs.Paid.PDROC_OverlayLaw_002
public import PaperProofs.Paid.PDROC_SimulatorFlow_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem overlayEventualStageSample_of_entry
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry) :
    overlayEventualStageSample P fee hfee C accounting source stage sample =
      (((((sample.1.1, some (overlayShadow P source sample.1 entry)),
        overlayShadow P source sample.1 entry), sample.1.2.1 stage)),
        (sample.1.2.2 stage, sample.2 stage)) := by
  simp only [overlayEventualStageSample, sourceEventualHistorySeed, overlayVirtualEntryGate,
    overlayVirtualEntry, he, Option.map_some, Option.getD_some]
  rfl

/-- Decode the optional source only on the actual entry supplied here. -/
theorem overlay_entry_drawGood_of_optional_stageSample
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hgood : let s := overlayEventualStageSample P fee hfee C accounting source stage sample
      ∃ draw : SimulatorDraw P.sharedInstance,
        simulatorDrawAt P 0 (by norm_num) (sourceForOptionalHistory source) stage s.1.1.1 s.1.1.2 s.1.2 = some draw ∧
        sourceDrawGuardGood (sourceForOptionalHistory source) stage
          ((s.1.1, draw), overlayRowVirtualTruth P fee hfee draw.record s.2.2.1 (s.2.1, s.2.2.2))) :
    ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, overlayShadow P source sample.1 entry), draw),
            overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) := by
  intro entry he
  dsimp only at hgood
  rw [overlayEventualStageSample_of_entry P fee hfee C accounting source stage sample entry he] at hgood
  obtain ⟨draw, hd, hg⟩ := hgood
  refine ⟨draw, ?_, ?_⟩
  · change simulatorDrawAt P 0 (by norm_num) source stage sample.1.1
      (overlayShadow P source sample.1 entry) (sample.1.2.1 stage) = some draw
    exact (simulatorDrawAt_optionalHistory_some P 0 (by norm_num) source stage sample.1.1
      (overlayShadow P source sample.1 entry)
      (overlayShadow P source sample.1 entry) (sample.1.2.1 stage)).symm.trans hd
  · exact (sourceDrawGuardGood_optionalHistory_some source stage sample.1.1
      (overlayShadow P source sample.1 entry)
      (overlayShadow P source sample.1 entry) draw _).mp hg

/-- The Root law's precise Good event supplies the actual finite auxiliary
sample and the concrete source guard, without a source-law premise. -/
theorem overlay_entry_drawGood_of_eventualReportedDraw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (overlayEventualReportedDraw P fee hfee C accounting source stage sample)) :
    ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, overlayShadow P source sample.1 entry), draw),
            overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) := by
  apply overlay_entry_drawGood_of_optional_stageSample P fee hfee C accounting source stage sample
  let s := overlayEventualStageSample P fee hfee C accounting source stage sample
  let drawAt := simulatorDrawAt P 0 (by norm_num) (sourceForOptionalHistory source) stage s.1.1.1 s.1.1.2 s.1.2
  change ∃ draw, drawAt = some draw ∧
    sourceDrawGuardGood (sourceForOptionalHistory source) stage
      ((s.1.1, draw), overlayRowVirtualTruth P fee hfee (simulatorDrawRecord drawAt) s.2.2.1 (s.2.1, s.2.2.2)) at hgood
  obtain ⟨draw, hd, hg⟩ := hgood
  refine ⟨draw, hd, ?_⟩
  simpa only [hd, simulatorDrawRecord, Option.map_some, Option.getD_some] using hg

/-- Normalize the whole eventual-exit random variable, retaining the old
seed, full virtual entry and complete stage-exit history. -/
theorem overlayEventualStageExit_of_entry_draw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw) :
    overlayEventualStageExit P fee hfee C accounting source stage sample =
      ((sample.1.1, some (overlayShadow P source sample.1 entry)),
        some (sourceDrawStageExit source stage
          (((sample.1.1, overlayShadow P source sample.1 entry), draw),
            overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))).2) := by
  let shadow := overlayShadow P source sample.1 entry
  have hsample : overlayEventualStageSample P fee hfee C accounting source stage sample =
      (((((sample.1.1, some shadow), shadow), sample.1.2.1 stage)), (sample.1.2.2 stage, sample.2 stage)) :=
    overlayEventualStageSample_of_entry P fee hfee C accounting source stage sample entry he
  have hdraw : simulatorDrawAt P 0 (by norm_num) (sourceForOptionalHistory source) stage
      (sample.1.1, some shadow) shadow (sample.1.2.1 stage) = some draw := by
    rw [simulatorDrawAt_optionalHistory_some]
    exact hd
  simp only [overlayEventualStageExit, hsample, overlayMixedSampledStageExit,
    overlaySampledStageExit, hdraw, overlayOptionalStageExit, overlayCoupledRecordTruth,
    sourceOptionalDrawStageExit, simulatorDrawRecord, Option.map_some, Option.getD_some]
  rw [sourceDrawStageExit_optionalHistory_some]
  rfl

end PDROC
