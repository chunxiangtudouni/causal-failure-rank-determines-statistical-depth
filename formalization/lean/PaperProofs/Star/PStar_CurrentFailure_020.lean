module

public import PaperProofs.Star.PStar_CurrentStop_017

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentFailure020

open Common Common.Native Parameters PStarLR PStarCurrentStop017
  PStarCurrentBlocked015 PStarSingletonsAbort016

theorem halted_failure_has_abandon (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes n state) (halted : state.halted = true) (failed : ¬state.ledger.success C) :
    ∃ clock old, Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes clock old ∧ old.halted = false ∧
      P.starReferenceRule order .current r none seed old.history = .abandon ∧
      state.ledger.written = old.ledger.written ∧ state.ledger.truth = old.ledger.truth := by
  cases path with
  | initial => cases halted
  | @next clock old next earlier step =>
    generalize selected : P.starReferenceRule order .current r none seed old.history = action at step
    cases step <;> try cases halted
    case next.stop.refl =>
      have active : old.halted = false := by assumption
      exact (failed (current_stop_success P order r C early accounting seed truth tapes earlier active selected)).elim
    case next.abandon.refl =>
      have active : old.halted = false := by assumption
      exact ⟨clock, old, earlier, active, selected, rfl, rfl⟩

theorem universalFirst_halted_failure_two_errors (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .universalFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .universalFirst)) {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) seed truth tapes n state)
    (halted : state.halted = true) (failed : ¬state.ledger.success C) :
    state.ledger.written (universalStage P.tools .universalFirst) =
      some (!state.ledger.truth (universalStage P.tools .universalFirst)) ∧
    state.ledger.written (singletonStage P.tools .universalFirst P.firstTool) =
      some (!state.ledger.truth (singletonStage P.tools .universalFirst P.firstTool)) := by
  obtain ⟨clock, old, earlier, active, selected, writes, truths⟩ :=
    halted_failure_has_abandon P .universalFirst r C early accounting seed truth tapes path halted failed
  rw [writes, truths]
  exact universalFirst_abandon_two_errors P r C early accounting seed truth tapes earlier active selected

theorem singletonsFirst_halted_failure_all_errors (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .singletonsFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .singletonsFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .singletonsFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .singletonsFirst)) {n : ℕ} {state : State (starInstance P.tools .singletonsFirst)}
    (path : Prefix (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes n state)
    (halted : state.halted = true) (failed : ¬state.ledger.success C) :
    ∀ stage : (starInstance P.tools .singletonsFirst).Stage,
      state.ledger.written stage = some (!state.ledger.truth stage) := by
  obtain ⟨clock, old, earlier, active, selected, writes, truths⟩ :=
    halted_failure_has_abandon P .singletonsFirst r C early accounting seed truth tapes path halted failed
  rw [writes, truths]
  exact singletonsFirst_abandon_all_errors P r C early accounting seed truth tapes earlier active selected

end PaperProofs.Star.PStarCurrentFailure020
