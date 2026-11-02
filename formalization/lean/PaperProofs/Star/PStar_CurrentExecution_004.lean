module

public import PaperProofs.Star.PStar_CurrentAllocation_003
public import PaperProofs.Common.NativeBellmanLower

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentExecution004

open Common Common.Native Parameters PStarLR PStarCurrentSelection002

/-- THIS current script executes only an existing compatible commitment,
using its genuine handle, unused execution tool/stage and true live cursor. -/
theorem current_selected_execute_guards (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order .current r limit seed state.history = .execute handle tool) :
    validHandle state handle ∧ tool ∈ (starInstance P.tools order).eligible handle.stage ∧
      (∃ allocation ∈ state.ledger.commitments, allocation.handle = handle ∧ allocation.tool = tool) ∧
      (∀ execution ∈ state.ledger.executions, execution.tool ≠ tool) ∧
      (∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ handle.stage) ∧ state.cursor = handle.stage.val := by
  have correcting : IsCorrection (P.starReferenceRule order .current r limit seed state.history) := by
    rw [selected]
    trivial
  obtain ⟨stage, cursor, _wrong, repair⟩ := current_rule_correction_selection P order r limit seed state.history correcting
  obtain ⟨member, hstage, noExec⟩ :=
    repairAction_execute_advance_selection P order state.history stage _ handle tool (repair.symm.trans selected)
  rw [prefix_historyCommitments (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path] at member
  obtain ⟨allocation, allocMember, allocEq⟩ := List.mem_map.mp member
  have hhandle : allocation.handle = handle := congrArg Prod.fst allocEq
  have htool : allocation.tool = tool := congrArg Prod.snd allocEq
  have invariant := prefix_invariant (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path
  have valid : validHandle state handle := by
    have genuine := invariant.commitment_genuine allocation allocMember
    obtain ⟨time, reported, _before⟩ := invariant.wellFormed.reported allocation allocMember
    refine ⟨?_, ?_, time, ?_⟩
    · rw [← hhandle]
      exact genuine.1
    · rw [← hhandle]
      exact genuine.2
    · rw [← hhandle]
      exact reported
  have compatible : tool ∈ (starInstance P.tools order).eligible handle.stage := by
    have usable := prefix_commitments_usable (P.input order) C accounting
      (P.starReferenceRule order .current r limit) Finset.univ
      (usesOnly_univ (P.input order) C accounting (P.starReferenceRule order .current r limit))
      seed truth tapes path allocation allocMember
    rw [hhandle, htool] at usable
    exact usable.2
  have uncorrected : ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ handle.stage := by
    intro execution executed equalStage
    have visible : (execution.handle, execution.tool) ∈ historyExecutions state.history := by
      rw [prefix_historyExecutions (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r limit) seed truth tapes path]
      exact List.mem_map.mpr ⟨execution, executed, rfl⟩
    apply (List.any_eq_false.mp noExec) _ visible
    exact beq_iff_eq.mpr (equalStage.trans hstage)
  have unused : ∀ execution ∈ state.ledger.executions, execution.tool ≠ tool := by
    intro execution executed equalTool
    obtain ⟨backing, backingMember, backingHandle, backingTool, _time⟩ := invariant.wellFormed.backed execution executed
    have equalAllocation : backing = allocation :=
      List.inj_on_of_nodup_map invariant.wellFormed.commitment_tools backingMember allocMember
        (backingTool.trans (equalTool.trans htool.symm))
    have equalHandle : execution.handle = handle :=
      backingHandle.symm.trans ((congrArg Commitment.handle equalAllocation).trans hhandle)
    exact uncorrected execution executed (congrArg MismatchHandle.stage equalHandle)
  refine ⟨valid, compatible, ⟨allocation, allocMember, hhandle, htool⟩, unused, uncorrected, ?_⟩
  rw [hstage]
  exact (prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path).symm.trans cursor

theorem current_selected_execute_has_step (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order .current r limit seed state.history = .execute handle tool) :
    ∃ next, Step (P.input order) C .uncapped accounting tapes state
      (P.starReferenceRule order .current r limit seed state.history) next := by
  obtain ⟨valid, compatible, backed, unused, uncorrected, cursor⟩ := current_selected_execute_guards P order r limit C accounting
    seed truth tapes path handle tool selected
  rw [selected]
  exact ⟨_, Step.execute state handle tool active valid compatible backed unused uncorrected (fun _ => cursor) (Or.inl rfl)⟩

end PaperProofs.Star.PStarCurrentExecution004
