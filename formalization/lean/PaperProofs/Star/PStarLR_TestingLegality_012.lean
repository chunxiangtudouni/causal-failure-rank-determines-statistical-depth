module

public import PaperProofs.Star.PStarLR_ActionShape_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

theorem testingActionReal_cases (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (limit : Option ℕ)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) :
    P.testingActionReal order kind r limit history stage = .review stage ∨
      (∃ bit, P.testingActionReal order kind r limit history stage = .write stage bit) ∨
      P.testingActionReal order kind r limit history stage = .abandon := by
  classical
  unfold Parameters.testingActionReal
  split
  · simp
  · split
    · dsimp only
      split
      · simp
      · cases limit with
        | none => simp
        | some quota =>
          dsimp only
          split <;> simp
    · simp

theorem testingActionReal_legal_uncapped (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) (tapes : ReviewTapes (P.input order))
    (state : State (starInstance P.tools order)) (stage : (starInstance P.tools order).Stage)
    (live : liveStage state stage) (openPort : state.ledger.written stage = none) :
    ∃ next, Step (P.input order) C .uncapped accounting tapes state
      (P.testingActionReal order kind r limit state.history stage) next := by
  rcases testingActionReal_cases P order kind r limit state.history stage with
    review | ⟨bit, write⟩ | abandon
  · rw [review]
    exact ⟨_, Step.review state stage live openPort (Or.inl rfl)⟩
  · rw [write]
    exact ⟨_, Step.write state stage bit live openPort (Or.inl rfl)⟩
  · rw [abandon]
    exact ⟨_, Step.abandon state live.1⟩

end PStarLR
