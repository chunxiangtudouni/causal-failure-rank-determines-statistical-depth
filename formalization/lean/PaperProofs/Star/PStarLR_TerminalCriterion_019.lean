module

public import PaperProofs.Star.PStarLR_GoodBarrier_017
public import PaperProofs.Star.PStarLR_BadCorrection_018
public import PaperProofs.Star.PStarLR_OriginalLegality_015
public import PaperProofs.Star.PStarLR_TerminalHalt_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem retained_rule_at_complete_before (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false) (complete : allWritten state.ledger)
    (before : state.cursor < (starInstance P.tools order).stageCount) :
    P.starReferenceRule order kind r limit seed state.history = .advance ⟨state.cursor, before⟩ := by
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C mode accounting
    (P.starReferenceRule order kind r limit) seed truth tapes path
  let stage : (starInstance P.tools order).Stage := ⟨state.cursor, before⟩
  cases written : state.ledger.written stage with
  | none => exact (complete stage written).elim
  | some bit =>
    unfold Parameters.starReferenceRule Parameters.candidateWithTesting
    simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, before]
    rw [prefix_historyWritten (P.input order) C mode accounting
      (P.starReferenceRule order kind r limit) seed truth tapes path, written]
    cases kind with
    | current => exact (retained rfl).elim
    | earlyRetained | lateRetained => rfl

theorem retained_rule_at_complete_halting_action (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false) (complete : allWritten state.ledger)
    (selected : P.starReferenceRule order kind r limit seed state.history = .stop ∨
      P.starReferenceRule order kind r limit seed state.history = .abandon) :
    P.starReferenceRule order kind r limit seed state.history = P.barrierAction order state.history := by
  have notBefore : ¬state.cursor < (starInstance P.tools order).stageCount := by
    intro before
    have advance := retained_rule_at_complete_before P order kind retained r limit C mode accounting
      seed truth tapes path active complete before
    rw [advance] at selected
    rcases selected with stop | abandon
    · cases stop
    · cases abandon
  have terminal : state.cursor = (starInstance P.tools order).stageCount :=
    Nat.le_antisymm (prefix_cursorInvariant (P.input order) C mode accounting
      (P.starReferenceRule order kind r limit) seed truth tapes path).bound (Nat.le_of_not_gt notBefore)
  apply retained_rule_at_barrier P order kind retained r limit seed state.history
  · exact (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans active
  · exact (prefix_historyCursor (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans terminal

theorem stopState_success_of_barrier (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (terminalExecution : C.execution = .terminalBarrier) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (policy : PolicyRule (starInstance P.tools order) Seed) (seed : Seed)
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) (selected : P.barrierAction order state.history = .stop) :
    (stopState state false).ledger.success C := by
  classical
  have covers := barrierAction_stop_covers_mismatches P order C mode accounting policy seed truth tapes path complete selected
  refine ⟨?_, rfl, ?_, ?_⟩
  · change decide (allWritten state.ledger) = true
    exact decide_eq_true complete
  · simp only [Ledger.windowObligations, terminalAllocation, terminalExecution, reduceCtorEq,
      false_implies, implies_true, and_self]
  · intro stage
    change state.ledger.written stage = some (state.ledger.truth stage) ∨
      ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage
    by_cases correct : state.ledger.written stage = some (state.ledger.truth stage)
    · exact Or.inl correct
    · have wrong : stage ∈ PaperProofs.Retained.ordinaryMismatches state.ledger := by
        rw [PaperProofs.Retained.mem_ordinaryMismatches]
        cases written : state.ledger.written stage with
        | none => exact (complete stage written).elim
        | some bit => cases ht : state.ledger.truth stage <;> cases bit <;> simp_all
      exact Or.inr ((PaperProofs.Retained.mem_executedStages state.ledger stage).mp (covers wrong))

theorem retained_halted_good_success (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (terminalExecution : C.execution = .terminalBarrier) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (halted : state.halted = true) (complete : allWritten state.ledger)
    (good : (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools) :
    state.ledger.success C := by
  cases path with
  | initial => cases halted
  | @next n old next earlier step =>
    generalize haction : P.starReferenceRule order kind r limit seed old.history = action at step
    cases step <;> try cases halted
    case next.stop.refl =>
      have active : old.halted = false := by assumption
      change allWritten old.ledger at complete
      have barrier := retained_rule_at_complete_halting_action P order kind retained r limit C mode accounting
        seed truth tapes earlier active complete (Or.inl haction)
      exact stopState_success_of_barrier P order C terminalAllocation terminalExecution mode accounting
        (P.starReferenceRule order kind r limit) seed truth tapes earlier complete (barrier.symm.trans haction)
    case next.abandon.refl =>
      have active : old.halted = false := by assumption
      change allWritten old.ledger at complete
      change (PaperProofs.Retained.ordinaryMismatches old.ledger).card ≤ P.tools at good
      have barrier := retained_rule_at_complete_halting_action P order kind retained r limit C mode accounting
        seed truth tapes earlier active complete (Or.inr haction)
      exact (barrierAction_ne_abandon_of_good P order C mode accounting (P.starReferenceRule order kind r limit)
        seed truth tapes earlier complete good (barrier.symm.trans haction)).elim

theorem retained_halted_card_criterion (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (terminalExecution : C.execution = .terminalBarrier) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (halted : state.halted = true) (complete : allWritten state.ledger) :
    (state.ledger.success C ↔ (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools) ∧
      state.ledger.executions.length = if (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools
        then (PaperProofs.Retained.ordinaryMismatches state.ledger).card else 0 := by
  classical
  have well := prefix_ledgerWellFormed (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
    seed truth tapes path
  have successIff : state.ledger.success C ↔ (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools := by
    constructor
    · intro success
      exact (PaperProofs.Retained.mismatches_matchable_of_success state.ledger C well success).card_le_tools
    · exact retained_halted_good_success P order kind retained r limit C terminalAllocation terminalExecution mode
        accounting seed truth tapes path halted complete
  refine ⟨successIff, ?_⟩
  split_ifs with good
  · have success := successIff.mpr good
    have executed := PaperProofs.Retained.executedStages_eq_mismatches_of_success state.ledger C well success
    have count : (PaperProofs.Retained.executedStages state.ledger).card = state.ledger.executions.length := by
      rw [PaperProofs.Retained.executedStages, List.toFinset_card_of_nodup well.execution_stages, List.length_map]
    exact count.symm.trans (congrArg Finset.card executed)
  · have empty := (retained_bad_prefix_no_corrections P order kind retained r limit C mode accounting
      seed truth tapes path complete (Nat.lt_of_not_ge good)).2
    rw [empty, List.length_nil]

theorem retained_terminalCriterion_of_ae_allWritten (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (terminalExecution : C.execution = .terminalBarrier) (accounting : NormalAccounting (starInstance P.tools order))
    (eventualWritten : ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())), ∃ start,
      allWritten (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample start).ledger) :
    P.TerminalCriterion order kind r C accounting := by
  have legal := retained_legal_uncapped P order kind retained r none C terminalAllocation terminalExecution accounting
    (Seed := Unit)
  filter_upwards [eventualWritten] with sample complete
  obtain ⟨start, complete⟩ := complete
  obtain ⟨n, later, halted⟩ := run_halts_after_allWritten (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) legal sample start complete
  have completeN : allWritten (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample n).ledger := by
    intro stage
    cases written : (run (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) sample start).ledger.written stage with
    | none => exact (complete stage written).elim
    | some bit =>
      have still := run_written_some_after (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) legal sample start (n-start) stage bit written
      rw [Nat.add_sub_of_le later] at still
      rw [still]
      exact Option.some_ne_none _
  obtain ⟨_clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) legal sample n
  have criterion := retained_halted_card_criterion P order kind retained r none C terminalAllocation terminalExecution
    .uncapped accounting sample.1 ((P.input order).truthAt sample.2) (worldTapes (P.input order) sample.2)
    path halted completeN
  refine ⟨n, ?_⟩
  dsimp only
  exact ⟨halted, completeN, criterion.1, fun _ => criterion.2⟩

end PStarLR
