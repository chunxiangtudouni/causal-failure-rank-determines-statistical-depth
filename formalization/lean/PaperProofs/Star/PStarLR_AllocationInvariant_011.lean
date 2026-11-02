module

public import PaperProofs.Star.PStarLR_RepairSelection_010
public import PaperProofs.Star.PStarLR_ReportedBarrier_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

def AllocationChoices (P : PaperProofs.Star.Parameters) (order : Order)
    (state : State (starInstance P.tools order)) : Prop :=
  ∀ allocation ∈ state.ledger.commitments,
    reportedError state.history allocation.handle.stage = true ∧
      P.retainedToolChoice order state.history allocation.handle.stage = some allocation.tool

set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_allocationChoices (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) : AllocationChoices P order state := by
  classical
  induction path with
  | initial => intro allocation member; cases member
  | @next n state next earlier step ih =>
    generalize haction : P.starReferenceRule order kind r limit seed state.history = action at step
    cases step with
    | review stage live port resources =>
      have before : state.cursor < (starInstance P.tools order).stageCount := by
        rw [live.2]
        exact stage.isLt
      have empty := (retained_prefix_no_corrections_before_terminal P order kind retained r limit
        C mode accounting seed truth tapes earlier before).1
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      rw [empty] at member
      cases member
    | write stage bit live port resources =>
      have before : state.cursor < (starInstance P.tools order).stageCount := by
        rw [live.2]
        exact stage.isLt
      have empty := (retained_prefix_no_corrections_before_terminal P order kind retained r limit
        C mode accounting seed truth tapes earlier before).1
      have newEmpty : (reportedWriteLedger C state stage bit).commitments = [] := by
        simp only [reportedWriteLedger]
        split_ifs <;> exact empty
      intro allocation member
      change allocation ∈ (reportedWriteLedger C state stage bit).commitments at member
      rw [newEmpty] at member
      cases member
    | advance stage live written resources =>
      have before : state.cursor < (starInstance P.tools order).stageCount := by
        rw [live.2]
        exact stage.isLt
      have empty := (retained_prefix_no_corrections_before_terminal P order kind retained r limit
        C mode accounting seed truth tapes earlier before).1
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      rw [empty] at member
      cases member
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
        rw [haction]
        trivial
      have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
      have historyActive : historyHalted state.history = false :=
        (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
          seed truth tapes earlier).trans active
      have barrier := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive terminal
      have selected : P.barrierAction order state.history = .allocate handle tool := barrier.symm.trans haction
      obtain ⟨stage, _size, wrong, _visible, chosen, _noCommit, _noExec, hstage⟩ :=
        barrierAction_allocate_selection P order state.history handle tool selected
      intro allocation member
      change allocation ∈ state.ledger.commitments ++ [⟨handle, tool, state.clock⟩] at member
      rcases List.mem_append.mp member with old | fresh
      · simpa only [record, Parameters.retainedToolChoice, reportedCorrect, reportedError,
          historyWritten, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil, eventWrite, eventReport, List.append_nil] using ih allocation old
      · have heq : allocation = ⟨handle, tool, state.clock⟩ := List.mem_singleton.mp fresh
        subst allocation
        simpa only [record, Parameters.retainedToolChoice, reportedCorrect, reportedError,
          historyWritten, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil, eventWrite, eventReport, List.append_nil, hstage] using
          (show reportedError state.history stage = true ∧
            P.retainedToolChoice order state.history stage = some tool from ⟨wrong, chosen⟩)
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      simpa only [record, Parameters.retainedToolChoice, reportedCorrect, reportedError,
        historyWritten, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, eventWrite, eventReport, List.append_nil] using ih allocation member
    | stop active =>
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      simpa only [stopState, Bool.false_eq_true, ↓reduceIte, Parameters.retainedToolChoice,
        reportedCorrect, reportedError, historyWritten, historyWrite, historyReport,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, eventWrite,
        eventReport, List.append_nil] using ih allocation member
    | abandon active =>
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      simpa only [stopState, ↓reduceIte, Parameters.retainedToolChoice,
        reportedCorrect, reportedError, historyWritten, historyWrite, historyReport,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, eventWrite,
        eventReport, List.append_nil] using ih allocation member

end PStarLR
