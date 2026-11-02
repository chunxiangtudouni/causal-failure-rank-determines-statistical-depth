module

public import PaperProofs.Paid.PDLower_Posterior_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem completedRecordDecision_actual_of_finite (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hf).World)
    (hfinite : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage ≠ ⊤) :
    completedRecordDecision P fee hf C accounting source stage
      (P.binarySymmetric.experiment.stoppedTranscript (pastEntryTest P fee hf C accounting source stage)
        ((P.input fee hf).preBirthView stage sample, (sample.2 stage).2)) =
      P.filledOrdinaryDecision fee hf C .uncapped accounting source.rule sample stage := by
  classical
  let count := P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage
  let pair : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape :=
    ((P.input fee hf).preBirthView stage sample, (sample.2 stage).2)
  let test := pastEntryTest P fee hf C accounting source stage
  have hstop : test.rule.stop pair.1 pair.2 = count := pastEntryTest_stop_eq_count P fee hf C accounting source stage sample
  have hword : (P.binarySymmetric.experiment.stoppedTranscript test pair).2 =
      (⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩ : P.binarySymmetric.experiment.StoppedWord) := by
    change (⟨(test.rule.stop pair.1 pair.2).toNat, fun k => pair.2 k.val⟩ : P.binarySymmetric.experiment.StoppedWord) = _
    rw [hstop]
  have hpast := pastEntryRecord_preBirth P fee hf C accounting source stage sample
  cases he : entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample with
  | none =>
    have hdec := actualOrdinaryDecision_none_of_no_entry P fee hf C .uncapped accounting source.rule source.legal sample stage he
    change completedRecordDecision P fee hf C accounting source stage (P.binarySymmetric.experiment.stoppedTranscript test pair) = _
    unfold completedRecordDecision
    simp only [show (P.binarySymmetric.experiment.stoppedTranscript test pair).1 = pair.1 from rfl]
    rw [hpast]
    simp only [entryHistorySeedRecord, he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Parameters.filledOrdinaryDecision, hdec, hword]
    change P.experiment.posteriorRecordDecision ((), ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩) = _
    change _ = if count = ⊤ then false else _
    rw [ite_eq_right hfinite]
  | some entry =>
    obtain ⟨start, hc, hb, hh⟩ := (entryHistory_some_iff (P.input fee hf) C.val .uncapped accounting source.rule stage sample entry).mp he
    have hfirst : FirstEntryAt (P.input fee hf) C.val .uncapped accounting source.rule stage.val start sample := ⟨hc, hb⟩
    have hdirect : headExitStop (P.input fee hf) stage (PDROC.simulatorPrewriteRule P source.rule)
        (sample.1, (run (P.input fee hf) C.val .uncapped accounting source.rule sample start).history)
          (worldTapes (P.input fee hf) sample.2 stage) = (count.toNat : ℕ∞) := by
      have h := eventualTest_stop_eq_count P fee hf C accounting source sample stage
      change (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
        (sample.1, entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample) _ = count at h
      rw [he, PDROC.sourceEventualEntryTest_stop_some P fee hf source.rule source.measurable_rule stage sample.1 entry
        (worldTapes (P.input fee hf) sample.2 stage), ← hh] at h
      exact h.trans (ENat.natCast_toNat hfinite).symm
    have hfilled := directFiniteStage_filledDecision P fee hf C accounting source sample start stage hfirst count.toNat hdirect
    obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hf) C.val .uncapped accounting source.rule source.legal sample stage.val start hfirst
    have hrun := PDROC.run_eq_entryReviewState_before_directExit P fee hf C.val accounting source.rule sample start stage ha hc
      (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 count.toNat (by rw [hdirect])
    have hhistory : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + count.toNat)).history =
        entry ++ recordReviewHistory P stage (P.binarySymmetric.experiment.stoppedTranscript test pair).2 := by
      rw [hrun, PDROC.entryReviewState_history, hh, hword]
      rfl
    change completedRecordDecision P fee hf C accounting source stage (P.binarySymmetric.experiment.stoppedTranscript test pair) = _
    unfold completedRecordDecision
    simp only [show (P.binarySymmetric.experiment.stoppedTranscript test pair).1 = pair.1 from rfl]
    rw [hpast]
    simp only [entryHistorySeedRecord, he, Option.isSome_some, ↓reduceIte, Option.getD_some]
    rw [← hhistory, hfilled]
    congr 1
    exact congrArg (fun word => P.experiment.posteriorRecordDecision ((), word)) hword

end PDLower
