module

public import PaperProofs.Star.Claims
public import PaperProofs.Common.NativeObservedWords
public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit

theorem run_prefix_of_active_no_legal {I : Instance} {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    (n : ℕ) (active : (run input C mode accounting rule sample n).halted = false) :
    Prefix input C mode accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n (run input C mode accounting rule sample n) := by
  classical
  induction n with
  | zero => exact .initial
  | succ n ih =>
    have old : (run input C mode accounting rule sample n).halted = false := by
      by_contra absent
      have halted : (run input C mode accounting rule sample n).halted = true :=
        Bool.eq_true_of_not_eq_false absent
      rw [run_succ_of_halted input C mode accounting rule sample n halted, halted] at active
      cases active
    have hp := ih old
    by_cases hex : ∃ next, Step input C mode accounting
        (frozenTapes input (frontierOf input (run input C mode accounting rule sample n) sample.2))
        (run input C mode accounting rule sample n)
        (rule sample.1 (run input C mode accounting rule sample n).history) next
    · have next : run input C mode accounting rule sample (n+1) = Classical.choose hex := by
        simp only [run, nextFromFrontier, old, Bool.false_eq_true, ↓reduceIte, dite_eq_left hex]
      rw [next]
      exact .next hp ((step_world_frontier_iff input C mode accounting sample.2 _ _ _).mpr
        (Classical.choose_spec hex))
    · simp [run, nextFromFrontier, old, hex, stopState] at active

theorem chosenTarget_congr (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (left right : List (VisibleEvent (starInstance P.tools order)))
    (writes : ∀ i, historyWritten left i = historyWritten right i)
    (reports : ∀ i, historyReport left i = historyReport right i)
    (i : (starInstance P.tools order).Stage) :
    P.chosenTargetReal order kind r left i = P.chosenTargetReal order kind r right i := by
  have errors (j : (starInstance P.tools order).Stage) :
      Parameters.reportedError left j = Parameters.reportedError right j := by
    simp only [Parameters.reportedError, writes, reports]
  have previous : Parameters.previousAllErrors left i = Parameters.previousAllErrors right i := by
    unfold Parameters.previousAllErrors
    simp_rw [errors]
  cases kind <;> cases order <;> simp only [Parameters.chosenTargetReal, errors, previous]

theorem chosenTarget_append_ignored (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (history : List (VisibleEvent (starInstance P.tools order)))
    (event : VisibleEvent (starInstance P.tools order))
    (writes : ∀ j, eventWrite j event = none) (reports : ∀ j, eventReport j event = none)
    (i : (starInstance P.tools order).Stage) :
    P.chosenTargetReal order kind r (history ++ [event]) i =
      P.chosenTargetReal order kind r history i := by
  apply chosenTarget_congr
  · intro j
    simp only [historyWritten, historyWrite, List.filterMap_append, List.filterMap_cons,
      writes, List.filterMap_nil, List.append_nil]
  · intro j
    simp only [historyReport, List.filterMap_append, List.filterMap_cons,
      reports, List.filterMap_nil, List.append_nil]

theorem rule_testing_of_live_unwritten (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {s : State (starInstance P.tools order)}
    (hp : Prefix (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) () truth tapes n s)
    (i : (starInstance P.tools order).Stage) (live : liveStage s i) (port : s.ledger.written i = none) :
    P.starReferenceRule order kind r none () s.history = P.testingActionReal order kind r none s.history i := by
  have hh := (prefix_historyHalted (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () truth tapes hp).trans live.1
  have hc := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () truth tapes hp
  have inside : historyCursor s.history < (starInstance P.tools order).stageCount := by
    rw [hc, live.2]
    exact i.isLt
  have stageEq : (⟨historyCursor s.history, inside⟩ : (starInstance P.tools order).Stage) = i :=
    Fin.ext (hc.trans live.2)
  unfold Parameters.starReferenceRule Parameters.candidateWithTesting
  simp only [hh, Bool.false_eq_true, ↓reduceIte, dite_eq_left inside, stageEq]
  rw [prefix_historyWritten (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () truth tapes hp i, port]

theorem testingAction_actual (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {s : State (starInstance P.tools order)}
    (hp : Prefix (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) () truth tapes n s)
    (i : (starInstance P.tools order).Stage) :
    P.testingActionReal order kind r none s.history i =
      match P.chosenTargetReal order kind r s.history i with
      | none => .write i false
      | some target =>
        if Real.log ((1-target)/target) ≤
            |P.channel.experiment.logOddsScore (tapes i) (s.ledger.reviews i).toNat| then
          .write i (decide (0 ≤ P.channel.experiment.logOddsScore (tapes i) (s.ledger.reviews i).toNat))
        else .review i := by
  classical
  have valid := prefix_historyObservation_alphabet (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () truth tapes hp i
  have score := prefix_historyObservationWord_score (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () truth tapes hp i valid
  cases ht : P.chosenTargetReal order kind r s.history i with
  | none => simp only [Parameters.testingActionReal, ht]
  | some target =>
    simp only [Parameters.testingActionReal, ht]
    split
    · change (if Real.log ((1-target)/target) ≤
          |((P.input order).experiment i).stoppedWordScore
            (historyObservationWord (P.input order) s.history i valid)| then
          Action.write i (decide (0 ≤ ((P.input order).experiment i).stoppedWordScore
            (historyObservationWord (P.input order) s.history i valid)))
        else Action.review i) = _
      dsimp only [Parameters.input] at valid score ⊢
      simp only [score]
    · exact False.elim (‹¬ _› valid)

end PDROC.StarFirstExit
