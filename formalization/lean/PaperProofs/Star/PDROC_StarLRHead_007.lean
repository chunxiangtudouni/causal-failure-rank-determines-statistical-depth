module

public import PaperProofs.Star.PDROC_StarLRHead_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem reference_run_advance_written (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (start : ℕ)
    (active : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).halted = false)
    (inside : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).cursor < (starInstance P.tools order).stageCount)
    (written : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).ledger.written
      ⟨(run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample start).cursor, inside⟩ ≠ none) :
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (start+1)).halted = false ∧
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (start+1)).cursor =
      (run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample start).cursor + 1 := by
  let state := run (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample start
  let stage : (starInstance P.tools order).Stage := ⟨state.cursor, inside⟩
  change state.halted = false at active
  change state.cursor < (starInstance P.tools order).stageCount at inside
  have legal := PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r none C
    late.2.1 late.2.2 accounting (Seed := Unit)
  obtain ⟨clock, _, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample start
  have historyActive := (prefix_historyHalted (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path
  change historyHalted state.history = false at historyActive
  change historyCursor state.history = state.cursor at historyCursorEq
  obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists'.mp written
  change state.ledger.written stage = some bit at hbit
  have selected : P.starReferenceRule order .lateRetained r none sample.1 state.history = .advance stage := by
    unfold Parameters.starReferenceRule Parameters.candidateWithTesting
    simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, inside]
    rw [prefix_historyWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path, hbit]
  have step := Step.advance (input := P.input order) (C := C) (mode := .uncapped)
    (accounting := accounting) (tapes := worldTapes (P.input order) sample.2)
    state stage ⟨active, rfl⟩ written (Or.inl rfl)
  have next := run_succ_of_step (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample start _ active
    (by rw [selected]; exact step)
  rw [next]
  exact ⟨rfl, rfl⟩

theorem reference_run_blind_write (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (start : ℕ)
    (active : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).halted = false)
    (inside : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).cursor < (starInstance P.tools order).stageCount)
    (nonzero : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).cursor ≠ 0)
    (openPort : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample start).ledger.written
      ⟨(run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample start).cursor, inside⟩ = none) :
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (start+1)).halted = false ∧
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (start+1)).cursor =
      (run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample start).cursor ∧
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (start+1)).ledger.written
      ⟨(run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample start).cursor, inside⟩ = some false := by
  let state := run (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample start
  let stage : (starInstance P.tools order).Stage := ⟨state.cursor, inside⟩
  change state.halted = false at active
  change state.cursor < (starInstance P.tools order).stageCount at inside
  change state.ledger.written stage = none at openPort
  change state.cursor ≠ 0 at nonzero
  have legal := PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r none C
    late.2.1 late.2.2 accounting (Seed := Unit)
  obtain ⟨clock, _, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample start
  have historyActive := (prefix_historyHalted (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path
  change historyHalted state.history = false at historyActive
  change historyCursor state.history = state.cursor at historyCursorEq
  have selected : P.starReferenceRule order .lateRetained r none sample.1 state.history = .write stage false := by
    unfold Parameters.starReferenceRule Parameters.candidateWithTesting
    simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, inside]
    rw [prefix_historyWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path, openPort]
    simp only [Parameters.testingActionReal, Parameters.chosenTargetReal, nonzero, ↓reduceIte]
    rfl
  have step := Step.write (input := P.input order) (C := C) (mode := .uncapped)
    (accounting := accounting) (tapes := worldTapes (P.input order) sample.2)
    state stage false ⟨active, rfl⟩ openPort (Or.inl rfl)
  have next := run_succ_of_step (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample start _ active
    (by rw [selected]; exact step)
  rw [next]
  refine ⟨rfl, rfl, ?_⟩
  classical
  change (reportedWriteLedger C state stage false).written stage = some false
  simp only [reportedWriteLedger]
  split_ifs <;> simp only [writeLedger, Function.update_self]

end PDROC.StarLRHead
