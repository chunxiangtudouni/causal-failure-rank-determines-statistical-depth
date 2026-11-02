module

public import PaperProofs.Star.PStarLR_RunFrame_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

def IsCorrection {I : Instance} : Action I → Prop
  | .allocate _ _ | .execute _ _ => True
  | _ => False

theorem testingActionReal_not_correction (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (limit : Option ℕ)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    ¬ IsCorrection (P.testingActionReal order kind r limit history stage) := by
  classical
  unfold Parameters.testingActionReal
  split
  · simp only [IsCorrection, not_false_eq_true]
  · split
    · dsimp only
      split
      · simp only [IsCorrection, not_false_eq_true]
      · cases limit with
        | none => simp only [IsCorrection, not_false_eq_true]
        | some quota =>
            dsimp only
            split <;> simp only [IsCorrection, not_false_eq_true]
    · simp only [IsCorrection, not_false_eq_true]

theorem star_retained_correction_cursor (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    {Seed : Type*} (seed : Seed) (history : List (VisibleEvent (starInstance P.tools order)))
    (correcting : IsCorrection (P.starReferenceRule order kind r limit seed history)) :
    historyCursor history = (starInstance P.tools order).stageCount := by
  unfold Parameters.starReferenceRule Parameters.candidateWithTesting at correcting
  split at correcting
  · exact False.elim correcting
  · split at correcting
    · dsimp only at correcting
      split at correcting
      · exact ((testingActionReal_not_correction P order kind r limit history _) correcting).elim
      · cases kind with
        | current => exact (retained rfl).elim
        | earlyRetained => exact False.elim correcting
        | lateRetained => exact False.elim correcting
    · split at correcting
      · assumption
      · exact False.elim correcting

theorem repairAction_ne_review (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Option (starInstance P.tools order).Tool)
    (done : Action (starInstance P.tools order)) (review : (starInstance P.tools order).Stage)
    (hdone : done ≠ .review review) :
    P.repairAction order history stage tool done ≠ .review review := by
  unfold Parameters.repairAction
  split
  · exact hdone
  · split
    · simp
    · split <;> simp

theorem barrierAction_ne_review (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (review : (starInstance P.tools order).Stage) :
    P.barrierAction order history ≠ .review review := by
  unfold Parameters.barrierAction
  dsimp only
  split
  · simp
  · split
    · simp
    · exact repairAction_ne_review P order history _ _ .stop review (by simp)

theorem lateRule_ne_review_of_cursor_ne_zero (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) {Seed : Type*} (seed : Seed)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (nonzero : historyCursor history ≠ 0) (review : (starInstance P.tools order).Stage) :
    P.starReferenceRule order .lateRetained r limit seed history ≠ .review review := by
  intro selected
  unfold Parameters.starReferenceRule Parameters.candidateWithTesting at selected
  split at selected
  · cases selected
  · split at selected
    · dsimp only at selected
      split at selected
      · simp only [Parameters.testingActionReal, Parameters.chosenTargetReal, nonzero, ↓reduceIte] at selected
        cases selected
      · cases selected
    · split at selected
      · exact (barrierAction_ne_review P order history review) selected
      · cases selected

end PStarLR
