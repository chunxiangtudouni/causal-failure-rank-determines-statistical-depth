module

public import PaperProofs.Paid.PDROC_Simulator_004
public import PaperProofs.Paid.PDROC_Simulator_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

theorem simulatorObservedScore_append_review {I : Instance}
    (history : List (VisibleEvent I)) (stage : I.Stage) (symbol : ℕ) :
    simulatorObservedScore (history ++ [.observation stage symbol]) stage =
      simulatorObservedScore history stage + if symbol = 1 then (1 : ℤ) else -1 := by
  simp [simulatorObservedScore, historyObservations, List.filterMap_append, eventObservation]

theorem simulatorObservedScore_headReview (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (entry : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (tape : P.binarySymmetric.experiment.Tape) (n : ℕ) :
    simulatorObservedScore (entry ++ headReviewHistory (P.input fee hfee) stage tape n) stage =
      simulatorObservedScore entry stage + P.binarySymmetric.signedSum tape n := by
  induction n with
  | zero => simp [headReviewHistory, P.binarySymmetric.signedSum_zero]
  | succ n ih =>
    have hs := headReviewHistory_succ (P.input fee hfee) stage tape n
    rw [hs, ← List.append_assoc, simulatorObservedScore_append_review, ih,
      P.binarySymmetric.signedSum_succ tape n]
    omega

theorem simulatorBoundaryAction_shape {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (record : AuxiliaryRecord) (coin decision : Bool)
    (hd : record.decision = some decision) :
    simulatorBoundaryAction history stage record coin = .review stage ∨
      ∃ bit, simulatorBoundaryAction history stage record coin = .write stage bit := by
  simp only [simulatorBoundaryAction, hd]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem simulatorBoundaryAction_allowed {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (record : AuxiliaryRecord) (coin decision : Bool)
    (hd : record.decision = some decision) (hcursor : historyCursor history = stage.val)
    (hwritten : historyWritten history stage = none) :
    historyAllowsAction history (simulatorBoundaryAction history stage record coin) := by
  rcases simulatorBoundaryAction_shape history stage record coin decision hd with hr | ⟨bit, hw⟩
  · rw [hr]; exact ⟨hcursor, hwritten⟩
  · rw [hw]; exact ⟨hcursor, hwritten⟩

theorem simulatorStageAt_some {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage)
    (hc : historyCursor history = stage.val) : simulatorStageAt history = some stage := by
  have ht : historyCursor history < I.compatibility.length := hc ▸ stage.isLt
  simp only [simulatorStageAt, ht, dite_true]
  congr 1
  exact Fin.ext hc

end PDROC
