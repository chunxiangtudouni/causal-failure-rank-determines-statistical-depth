module

public import PaperProofs.Star.PStar_CurrentImmediate_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentToolIdentity008

open Common Common.Native Parameters PStarLR PStarCurrentChoice001 PStarCurrentSelection002 PStarCurrentLegality006

def ToolIdentity (P : PaperProofs.Star.Parameters) (order : Order)
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools) : Prop :=
  match stageLabel P.tools order stage with
  | some label => tool.val = label.val
  | none => order = .universalFirst → tool.val = 0

theorem current_selected_allocate_identity (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) {Seed : Type*} (seed : Seed)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order .current r limit seed history = .allocate handle tool) :
    ToolIdentity P order handle.stage tool := by
  have correcting : IsCorrection (P.starReferenceRule order .current r limit seed history) := by
    rw [selected]
    trivial
  obtain ⟨stage, _cursor, _wrong, repair⟩ := current_rule_correction_selection P order r limit seed history correcting
  obtain ⟨_visible, chosen, _noCommit, _noExec, hstage⟩ :=
    repairAction_allocate_advance_selection P order history stage _ handle tool (repair.symm.trans selected)
  rw [hstage]
  unfold ToolIdentity
  cases label : stageLabel P.tools order stage with
  | some own => exact currentToolChoice_singleton_identity P order history stage tool own label chosen
  | none =>
    intro universalFirst
    subst order
    exact currentToolChoice_universalFirst_identity P history stage tool label chosen

/-- Each real original commitment records the selected static tool identity;
later observations/reports/abandon do not erase or reassign that allocation. -/
theorem prefix_allocationToolIdentity (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) :
    ∀ allocation ∈ state.ledger.commitments, ToolIdentity P order allocation.handle.stage allocation.tool := by
  induction path with
  | initial => intro allocation member; cases member
  | @next n state next earlier step ih =>
    generalize haction : P.starReferenceRule order .current r limit seed state.history = action at step
    cases step with
    | review => exact ih
    | write stage bit live port resources =>
      intro allocation member
      have frame : (reportedWriteLedger C state stage bit).commitments = state.ledger.commitments := by
        dsimp only [reportedWriteLedger]
        split_ifs <;> rfl
      change allocation ∈ (reportedWriteLedger C state stage bit).commitments at member
      rw [frame] at member
      exact ih allocation member
    | advance => exact ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro allocation member
      change allocation ∈ state.ledger.commitments ++ [⟨handle, tool, state.clock⟩] at member
      rcases List.mem_append.mp member with old | fresh
      · exact ih allocation old
      · have heq : allocation = ⟨handle, tool, state.clock⟩ := List.mem_singleton.mp fresh
        subst allocation
        exact current_selected_allocate_identity P order r limit seed state.history handle tool haction
    | execute => exact ih
    | stop => exact ih
    | abandon => exact ih

theorem prefix_executionToolIdentity (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (execution : Execution (starInstance P.tools order))
    (member : execution ∈ state.ledger.executions) :
    ToolIdentity P order execution.handle.stage execution.tool := by
  obtain ⟨allocation, allocated, hhandle, htool, _time⟩ :=
    (prefix_ledgerWellFormed (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path).backed execution member
  rw [← hhandle, ← htool]
  exact prefix_allocationToolIdentity P order r limit C accounting seed truth tapes path allocation allocated

theorem currentToolIdentities (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) :
    P.CurrentToolIdentities order r limit C accounting := by
  intro sample n execution member
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) (current_legal_uncapped P order r limit C accounting) sample n
  exact prefix_executionToolIdentity P order r limit C accounting sample.1 _ _ path execution member

end PaperProofs.Star.PStarCurrentToolIdentity008
