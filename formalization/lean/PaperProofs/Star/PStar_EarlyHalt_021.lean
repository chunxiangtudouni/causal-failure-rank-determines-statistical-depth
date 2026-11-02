module

public import PaperProofs.Star.PStarLR_LateHaltWritten_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarEarlyHalt021

open Common Common.Native Parameters PStarLR

theorem early_halting_action_terminal (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order .earlyRetained r none)
      seed truth tapes n state) (active : state.halted = false)
    (selected : P.starReferenceRule order .earlyRetained r none seed state.history = .stop ∨
      P.starReferenceRule order .earlyRetained r none seed state.history = .abandon) :
    state.cursor = (starInstance P.tools order).stageCount := by
  classical
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order .earlyRetained r none)
      seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C mode accounting
    (P.starReferenceRule order .earlyRetained r none) seed truth tapes path
  have notBefore : ¬state.cursor < (starInstance P.tools order).stageCount := by
    intro before
    let stage : (starInstance P.tools order).Stage := ⟨state.cursor, before⟩
    cases written : state.ledger.written stage with
    | none =>
      have choice : P.starReferenceRule order .earlyRetained r none seed state.history =
          P.testingActionReal order .earlyRetained r none state.history stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, before]
        rw [prefix_historyWritten (P.input order) C mode accounting
          (P.starReferenceRule order .earlyRetained r none) seed truth tapes path, written]
      rw [choice] at selected
      rcases selected with stop | abandon
      · rcases testingActionReal_cases P order .earlyRetained r none state.history stage with
          review | ⟨bit, write⟩ | given
        · rw [review] at stop
          cases stop
        · rw [write] at stop
          cases stop
        · rw [given] at stop
          cases stop
      · have valid : ∀ symbol ∈ historyObservations state.history stage,
            symbol < P.channel.experiment.alphabetSize := by
          intro symbol member
          exact prefix_historyObservation_alphabet (P.input order) C mode accounting
            (P.starReferenceRule order .earlyRetained r none) seed truth tapes path stage symbol member
        exact testingActionReal_noquota_ne_abandon P order .earlyRetained r state.history stage valid abandon
    | some bit =>
      have advance : P.starReferenceRule order .earlyRetained r none seed state.history = .advance stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, before]
        rw [prefix_historyWritten (P.input order) C mode accounting
          (P.starReferenceRule order .earlyRetained r none) seed truth tapes path, written]
      rw [advance] at selected
      rcases selected with stop | abandon
      · cases stop
      · cases abandon
  exact Nat.le_antisymm (prefix_cursorInvariant (P.input order) C mode accounting
    (P.starReferenceRule order .earlyRetained r none) seed truth tapes path).bound (Nat.le_of_not_gt notBefore)

theorem early_halted_prefix_allWritten (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order .earlyRetained r none)
      seed truth tapes n state) (halted : state.halted = true) : allWritten state.ledger := by
  cases path with
  | initial => cases halted
  | @next n old next earlier step =>
    generalize haction : P.starReferenceRule order .earlyRetained r none seed old.history = action at step
    cases step <;> try cases halted
    case next.stop.refl =>
      have active : old.halted = false := by assumption
      have terminal := early_halting_action_terminal P order r C mode accounting seed truth tapes earlier active (Or.inl haction)
      change allWritten old.ledger
      exact prefix_allWritten_of_terminal (P.input order) C mode accounting
        (P.starReferenceRule order .earlyRetained r none) seed truth tapes earlier terminal
    case next.abandon.refl =>
      have active : old.halted = false := by assumption
      have terminal := early_halting_action_terminal P order r C mode accounting seed truth tapes earlier active (Or.inr haction)
      change allWritten old.ledger
      exact prefix_allWritten_of_terminal (P.input order) C mode accounting
        (P.starReferenceRule order .earlyRetained r none) seed truth tapes earlier terminal


end PaperProofs.Star.PStarEarlyHalt021
