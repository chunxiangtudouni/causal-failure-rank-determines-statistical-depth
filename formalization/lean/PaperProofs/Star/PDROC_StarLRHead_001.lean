module

public import PaperProofs.Star.PStarLR_RealTestLaw_007
public import PaperProofs.Common.NativeHeadTest

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem headHistory_cursor {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    historyCursor (headReviewHistory input stage tape n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [headReviewHistory_succ, historyCursor, eventAdvance] using ih

theorem headHistory_written {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (other : I.Stage) :
    historyWritten (headReviewHistory input stage tape n) other = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [headReviewHistory_succ, historyWritten, historyWrite, eventWrite] using ih

theorem headHistory_active {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    historyHalted (headReviewHistory input stage tape n) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [headReviewHistory_succ, historyHalted, historyActions, eventAction] using ih

theorem headHistory_observations {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    historyObservations (headReviewHistory input stage tape n) stage =
      List.ofFn (fun k : Fin n => (tape k.val).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [headReviewHistory_succ]
    change (headReviewHistory input stage tape n ++
      [VisibleEvent.observation stage (tape n).val]).filterMap (eventObservation stage) = _
    rw [List.filterMap_append]
    rw [show ([VisibleEvent.observation stage (tape n).val] : List (VisibleEvent I)).filterMap
      (eventObservation stage) = [(tape n).val] by simp [eventObservation]]
    change historyObservations (headReviewHistory input stage tape n) stage ++ [(tape n).val] = _
    rw [ih, List.ofFn_succ_last]
    rfl

theorem headHistory_valid {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    ∀ symbol ∈ historyObservations (headReviewHistory input stage tape n) stage,
      symbol < (input.experiment stage).alphabetSize := by
  intro symbol hsymbol
  rw [headHistory_observations] at hsymbol
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hsymbol
  exact (tape k.val).isLt

theorem headHistory_score {I : Instance} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ)
    (valid : ∀ symbol ∈ historyObservations (headReviewHistory input stage tape n) stage,
      symbol < (input.experiment stage).alphabetSize) :
    (input.experiment stage).stoppedWordScore
      (historyObservationWord input (headReviewHistory input stage tape n) stage valid) =
      (input.experiment stage).logOddsScore tape n := by
  have hlen : (historyObservations (headReviewHistory input stage tape n) stage).length = n := by
    rw [headHistory_observations, List.length_ofFn]
  have hscore := (input.experiment stage).stoppedWordScore_eq_of_word_prefix
    (historyObservationWord input (headReviewHistory input stage tape n) stage valid) tape
    (by
      intro k
      apply Fin.ext
      simp only [historyObservationWord]
      simp [headHistory_observations])
  simpa only [historyObservationWord, hlen] using hscore

theorem reference_head_action (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (tape : P.channel.experiment.Tape) (n : ℕ) :
    P.starReferenceRule order .lateRetained r none (Seed := Unit) ()
      (headReviewHistory (P.input order) (firstStage P.tools order) tape n) =
      if Real.log ((1-r)/r) ≤ |P.channel.experiment.logOddsScore tape n| then
        .write (firstStage P.tools order) (decide (0 ≤ P.channel.experiment.logOddsScore tape n))
      else .review (firstStage P.tools order) := by
  classical
  have hstage : 0 < (starInstance P.tools order).stageCount := by rw [stageCount_eq]; omega
  generalize firstEq : firstStage P.tools order = head at ⊢
  have headval : head.val = 0 := (congrArg Fin.val firstEq).symm
  rcases head with ⟨value, headlt⟩
  change value = 0 at headval
  subst value
  have hword := headHistory_score (P.input order) ⟨0, headlt⟩ tape n
    (headHistory_valid (P.input order) ⟨0, headlt⟩ tape n)
  have hactive := headHistory_active (P.input order) ⟨0, headlt⟩ tape n
  have hcursor := headHistory_cursor (P.input order) ⟨0, headlt⟩ tape n
  have hwritten := headHistory_written (P.input order) ⟨0, headlt⟩ tape n ⟨0, headlt⟩
  unfold Parameters.starReferenceRule
  unfold Parameters.candidateWithTesting
  rw [hactive, hcursor]
  simp only [Bool.false_eq_true, ↓reduceIte, dite_eq_left hstage]
  change (match historyWritten (headReviewHistory (P.input order) ⟨0, headlt⟩ tape n)
      ⟨0, headlt⟩ with
    | none => _
    | some _ => _) = _
  rw [hwritten]
  simp only [Parameters.testingActionReal, Parameters.chosenTargetReal, ite_eq_left]
  split
  · change (if Real.log ((1-r)/r) ≤
        |((P.input order).experiment ⟨0, headlt⟩).stoppedWordScore
          (historyObservationWord (P.input order)
            (headReviewHistory (P.input order) ⟨0, headlt⟩ tape n)
            ⟨0, headlt⟩ _)| then _ else _) = _
    dsimp only [Parameters.input] at hword ⊢
    simp only [hword]
  · exact False.elim (‹¬ _› (headHistory_valid (P.input order) ⟨0, headlt⟩ tape n))

theorem reference_head_stop (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (tape : P.channel.experiment.Tape) :
    headExitStop (P.input order) (firstStage P.tools order)
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)) () tape =
      realPosteriorStop P.channel.experiment r tape := by
  classical
  unfold headExitStop realPosteriorStop
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, reference_head_action]
  apply exists_congr
  intro n
  by_cases hit : Real.log ((1-r)/r) ≤ |P.channel.experiment.logOddsScore tape n| <;>
    simp [hit]

theorem reference_run_before_stop (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (n : ℕ)
    (before : (n : ℕ∞) ≤ realPosteriorStop P.channel.experiment r
      ((P.input order).reviewAt sample.2 (firstStage P.tools order))) :
    run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n =
      headReviewState (P.input order) accounting (firstStage P.tools order)
        ((P.input order).truthAt sample.2)
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) n := by
  apply run_eq_headReviewState (hhead := rfl)
  cases sample.1
  exact before.trans_eq (reference_head_stop P order r
    ((P.input order).reviewAt sample.2 (firstStage P.tools order))).symm

end PDROC.StarLRHead
