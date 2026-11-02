module

public import PaperProofs.Star.PStar_CurrentExecution_004
public import PaperProofs.Star.PStarLR_TestingLegality_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentCases005

open Common Common.Native Parameters PStarLR

/-- The original current post-write routine has exactly its four actual
outcomes; completed corrections advance, failed tool choices abandon. -/
theorem repairAction_advance_cases (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) :
    P.repairAction order history stage choice (.advance stage) = .advance stage ∨
      P.repairAction order history stage choice (.advance stage) = .abandon ∨
      (∃ handle tool, P.repairAction order history stage choice (.advance stage) = .allocate handle tool) ∨
      (∃ handle tool, P.repairAction order history stage choice (.advance stage) = .execute handle tool) := by
  unfold Parameters.repairAction
  split
  · simp
  · split
    · simp
    · split <;> simp

/-- Actual Prefix-written ports select real post-write correction actions.
This does not assume success, risk, completion or native original-cap H0. -/
theorem current_written_action_cases (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (active : state.halted = false)
    (current : state.cursor < (starInstance P.tools order).stageCount) (bit : Bool)
    (written : state.ledger.written ⟨state.cursor, current⟩ = some bit) :
    let stage : (starInstance P.tools order).Stage := ⟨state.cursor, current⟩
    P.starReferenceRule order .current r limit seed state.history = .advance stage ∨
      P.starReferenceRule order .current r limit seed state.history = .abandon ∨
      (∃ handle tool, P.starReferenceRule order .current r limit seed state.history = .allocate handle tool) ∨
      (∃ handle tool, P.starReferenceRule order .current r limit seed state.history = .execute handle tool) := by
  let stage : (starInstance P.tools order).Stage := ⟨state.cursor, current⟩
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path
  have selected : P.starReferenceRule order .current r limit seed state.history =
      match historyReport state.history stage with
      | none => .abandon
      | some _ => if reportedError state.history stage then
          P.repairAction order state.history stage (P.currentToolChoice order state.history stage) (.advance stage)
        else .advance stage := by
    unfold Parameters.starReferenceRule Parameters.candidateWithTesting
    simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, current]
    rw [prefix_historyWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path, written]
    rfl
  dsimp only
  rw [selected]
  cases reported : historyReport state.history stage with
  | none => exact Or.inr (Or.inl rfl)
  | some pair =>
    dsimp only
    by_cases wrong : reportedError state.history stage = true
    · rw [ite_eq_left wrong]
      exact repairAction_advance_cases P order state.history stage (P.currentToolChoice order state.history stage)
    · rw [ite_eq_right wrong]
      exact Or.inl rfl

end PaperProofs.Star.PStarCurrentCases005
