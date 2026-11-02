module

public import PaperProofs.Star.PStar_CountIdealRisk_025

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountTerminal029

open Common Common.Native Parameters MeasureTheory PStarLR PStarActualHalt022
  PStarCurrentFailure020 PStarEarlyHalt021

theorem success_allWritten {I : Instance} (ledger : Ledger I) (C : Contract I)
    (well : LedgerWellFormed ledger) (success : ledger.success C) : allWritten ledger := by
  intro stage unwritten
  rcases success.2.2.2 stage with correct | ⟨execution, member, equalStage⟩
  · rw [unwritten] at correct
    cases correct
  · have wrong := well.genuine execution member
    rw [equalStage, unwritten] at wrong
    cases wrong.1

theorem singletonsFirst_halted_allWritten (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .singletonsFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .singletonsFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .singletonsFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .singletonsFirst)) {n : ℕ} {state : State (starInstance P.tools .singletonsFirst)}
    (path : Prefix (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes n state)
    (halted : state.halted = true) : allWritten state.ledger := by
  classical
  by_cases success : state.ledger.success C
  · exact success_allWritten state.ledger C (prefix_ledgerWellFormed (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path) success
  · have wrong := singletonsFirst_halted_failure_all_errors P r C early accounting seed truth tapes path halted success
    intro stage
    rw [wrong stage]
    exact Option.some_ne_none _

theorem singletonsFirst_halted_criterion (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .singletonsFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .singletonsFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .singletonsFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .singletonsFirst)) {n : ℕ} {state : State (starInstance P.tools .singletonsFirst)}
    (path : Prefix (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes n state)
    (halted : state.halted = true) :
    state.ledger.success C ↔ (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools := by
  classical
  constructor
  · intro success
    exact (PaperProofs.Retained.mismatches_matchable_of_success state.ledger C
      (prefix_ledgerWellFormed (P.input .singletonsFirst) C .uncapped accounting
        (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path) success).card_le_tools
  · intro good
    by_contra failure
    have wrong := singletonsFirst_halted_failure_all_errors P r C early accounting seed truth tapes path halted failure
    have full : PaperProofs.Retained.ordinaryMismatches state.ledger =
        (Finset.univ : Finset (starInstance P.tools .singletonsFirst).Stage) := by
      ext stage
      simp only [PaperProofs.Retained.mem_ordinaryMismatches, Finset.mem_univ, iff_true]
      exact wrong stage
    have count : (PaperProofs.Retained.ordinaryMismatches state.ledger).card = P.tools+1 := by
      rw [full]
      simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
      exact stageCount_eq P.tools .singletonsFirst
    rw [count] at good
    omega

theorem currentSingletons_terminalCriterion (P : PaperProofs.Star.Parameters)
    (C : Contract (starInstance P.tools .singletonsFirst)) (qualified : C.IsCurrentAllocation)
    (accounting : NormalAccounting (starInstance P.tools .singletonsFirst)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) : P.TerminalCriterion .singletonsFirst .current r C accounting := by
  filter_upwards [original_halts_ae P .singletonsFirst .current r positive quarter C qualified accounting]
    with sample termination
  obtain ⟨n, halted⟩ := termination
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input .singletonsFirst) C .uncapped accounting
    (P.starReferenceRule .singletonsFirst .current r none)
    (reference_legal P .singletonsFirst .current r C qualified accounting) sample n
  refine ⟨n, halted, ?_, ?_, ?_⟩
  · exact singletonsFirst_halted_allWritten P r C qualified.1 accounting sample.1 _ _ path halted
  · exact singletonsFirst_halted_criterion P r C qualified.1 accounting sample.1 _ _ path halted
  · intro impossible
    exact (impossible rfl).elim

theorem earlyRetained_terminalCriterion (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (qualified : C.IsEarlyRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) : P.TerminalCriterion order .earlyRetained r C accounting := by
  apply retained_terminalCriterion_of_ae_allWritten P order .earlyRetained (by decide) r C qualified.2.1 qualified.2.2 accounting
  filter_upwards [original_halts_ae P order .earlyRetained r positive quarter C qualified accounting]
    with sample termination
  obtain ⟨n, halted⟩ := termination
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .earlyRetained r none)
    (reference_legal P order .earlyRetained r C qualified accounting) sample n
  exact ⟨n, early_halted_prefix_allWritten P order r C .uncapped accounting sample.1 _ _ path halted⟩

theorem countTerminalCriterion (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) : P.TerminalCriterion order kind r C accounting := by
  rcases countKind with rfl | ⟨rfl, rfl⟩
  · exact earlyRetained_terminalCriterion P order C qualified accounting r positive quarter
  · exact currentSingletons_terminalCriterion P C qualified accounting r positive quarter

end PaperProofs.Star.PStarCountTerminal029
