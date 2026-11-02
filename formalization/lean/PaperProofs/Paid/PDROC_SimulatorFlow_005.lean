module

public import PaperProofs.Paid.PDROC_SimulatorFlow_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Shared finite-stop decoder witness for actual source flow and terminal
capture. The draw retains its original whole word, action and reported truth. -/
theorem sourceEventualReportedDraw_source_realization_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤)
    (history : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample = some history) :
    ∃ (start : ℕ) (draw : SimulatorDraw P.sharedInstance),
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source.rule stage.val start sample ∧
      (run (P.input fee hfee) C.val .uncapped accounting source.rule sample start).history = history ∧
      simulatorDrawAt P fee hfee source.rule stage sample.1
        (run (P.input fee hfee) C.val .uncapped accounting source.rule sample start).history
          (worldTapes (P.input fee hfee) sample.2 stage) = some draw ∧
      sourceEventualReportedDraw P fee hfee C accounting source stage sample =
        (((((sample.1, some history), history), draw), (P.input fee hfee).truthAt sample.2 stage)) := by
  let input := P.input fee hfee
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  obtain ⟨start, hc, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C.val .uncapped accounting source.rule stage sample history).mp he
  have hsample : sourceEventualStageSample P fee hfee C accounting source stage sample =
    (((sample.1, some history), history), sample.2 stage) := by
    change (sourceEventualHistorySeed (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample), _) = _
    rw [he]
    rfl
  let draw := (sourceEventualReportedDraw P fee hfee C accounting source stage sample).1.2
  have hs' : (simulatorLocalTest P fee hfee wrapped hm stage).rule.stop
    ((sample.1, some history), history) (sample.2 stage).2 ≠ ⊤ := by
    rw [hsample] at hs
    exact hs
  have hd0 := simulatorDrawAt_eq_decoder_of_finite P fee hfee wrapped hm stage
    ((((sample.1, some history), history), (sample.2 stage).2)) hs'
  have hdraw : draw = simulatorDrawDecoder P fee hfee wrapped stage
    (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee wrapped hm stage)
      ((((sample.1, some history), history), (sample.2 stage).2))) := by
    change (sourceDirectReportedDraw P fee hfee wrapped hm stage
    (sourceEventualStageSample P fee hfee C accounting source stage sample)).1.2 = _
    rw [hsample]
    rfl
  have hdw : simulatorDrawAt P fee hfee wrapped stage (sample.1, some history) history (sample.2 stage).2 = some draw :=
    hd0.trans (congrArg some hdraw.symm)
  have hdSource : simulatorDrawAt P fee hfee source.rule stage sample.1 history (sample.2 stage).2 = some draw :=
    (simulatorDrawAt_optionalHistory_some P fee hfee source.rule stage sample.1 history history (sample.2 stage).2).symm.trans hdw
  have hd : simulatorDrawAt P fee hfee source.rule stage sample.1
    (run input C.val .uncapped accounting source.rule sample start).history
      (worldTapes input sample.2 stage) = some draw :=
    (congrArg (fun entry => simulatorDrawAt P fee hfee source.rule stage sample.1 entry
    ((sample.2 stage).2 : P.experiment.Tape)) hhistory).trans hdSource
  have hcoords : (sourceEventualReportedDraw P fee hfee C accounting source stage sample).1.1 =
    ((sample.1, some history), history) := by
    change (sourceEventualStageSample P fee hfee C accounting source stage sample).1 = _
    rw [hsample]
  have hreport : sourceEventualReportedDraw P fee hfee C accounting source stage sample =
    (((((sample.1, some history), history), draw), input.truthAt sample.2 stage)) :=
    Prod.ext (Prod.ext hcoords rfl) rfl
  exact ⟨start, draw, ⟨hc, hbefore⟩, hhistory, hd, hreport⟩

/-- The exact whole-sample source flow through its measurable reported-draw
kernel. Never-entry remains none; local finiteness is the sole path condition. -/
theorem sourceEventualReportedDraw_nextEntry_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage next : P.sharedInstance.Stage) (hnext : next.val = stage.val + 1)
    (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤) :
    entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule next sample =
      simulatorNextEntryProjection next (sourceDrawStageExit (sourceForOptionalHistory source.rule) stage
        (sourceEventualReportedDraw P fee hfee C accounting source stage sample)) := by
  let input := P.input fee hfee
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  cases he : entryHistory input C.val .uncapped accounting source.rule stage sample with
  | none =>
    have hn := entryHistory_next_none_of_prior_none input C.val .uncapped accounting source.rule source.legal
      sample stage next (by omega) he
    have hseed : (sourceDrawStageExit wrapped stage
        (sourceEventualReportedDraw P fee hfee C accounting source stage sample)).1 = (sample.1, none) := by
      change (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample) = _
      rw [he]
    change (sourceDrawStageExit (sourceForOptionalHistory source.rule) stage
      (sourceEventualReportedDraw P fee hfee C accounting source stage sample)).1 = (sample.1, none) at hseed
    change (sample.1, entryHistory input C.val .uncapped accounting source.rule next sample) = _
    rw [hn]
    simp only [simulatorNextEntryProjection, hseed, Option.isSome_none, Bool.false_eq_true,
      false_and, ↓reduceIte]
  | some history =>
    obtain ⟨start, draw, hfirst, hhistory, hd, hreport⟩ :=
      sourceEventualReportedDraw_source_realization_of_finite P fee hfee C accounting source stage sample hs history he
    rw [hreport]
    have h := source_nextEntry_projection_of_finiteDraw P fee hfee C accounting source.rule source.legal
      sample start stage next hnext hfirst draw hd
    rw [hhistory] at h
    exact h
end PDROC

