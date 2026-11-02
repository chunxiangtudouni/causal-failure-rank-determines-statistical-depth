module

public import PaperProofs.Star.PStarLR_AllocationLegality_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem retained_selected_execute_guards (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order kind r limit seed state.history = .execute handle tool) :
    validHandle state handle ∧ tool ∈ (starInstance P.tools order).eligible handle.stage ∧
      (∃ allocation ∈ state.ledger.commitments, allocation.handle = handle ∧ allocation.tool = tool) ∧
      (∀ execution ∈ state.ledger.executions, execution.tool ≠ tool) ∧
      (∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ handle.stage) := by
  classical
  have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
    rw [selected]
    trivial
  have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans active
  have barrier := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive terminal
  obtain ⟨stage, _size, _wrong, member, hstage, noExec⟩ :=
    barrierAction_execute_selection P order state.history handle tool (barrier.symm.trans selected)
  rw [prefix_historyCommitments (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
    seed truth tapes path] at member
  obtain ⟨allocation, allocMember, allocEq⟩ := List.mem_map.mp member
  have hhandle : allocation.handle = handle := congrArg Prod.fst allocEq
  have htool : allocation.tool = tool := congrArg Prod.snd allocEq
  have invariant := prefix_invariant (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
    seed truth tapes path
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
    have chosen := (prefix_allocationChoices P order kind retained r limit C mode accounting
      seed truth tapes path allocation allocMember).2
    have chosen' : P.retainedToolChoice order state.history handle.stage = some tool := by
      rw [← hhandle, ← htool]
      exact chosen
    exact retainedToolChoice_compatible P order state.history handle.stage tool chosen'
  have uncorrected : ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ handle.stage := by
    intro execution executed equalStage
    have visible : (execution.handle, execution.tool) ∈ historyExecutions state.history := by
      rw [prefix_historyExecutions (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
        seed truth tapes path]
      exact List.mem_map.mpr ⟨execution, executed, rfl⟩
    apply (List.any_eq_false.mp noExec) _ visible
    exact beq_iff_eq.mpr (equalStage.trans hstage)
  have unused : ∀ execution ∈ state.ledger.executions, execution.tool ≠ tool := by
    intro execution executed equalTool
    obtain ⟨backing, backingMember, backingHandle, backingTool, _time⟩ :=
      invariant.wellFormed.backed execution executed
    have equalAllocation : backing = allocation :=
      List.inj_on_of_nodup_map invariant.wellFormed.commitment_tools backingMember allocMember
        (backingTool.trans (equalTool.trans htool.symm))
    have equalHandle : execution.handle = handle :=
      backingHandle.symm.trans ((congrArg Commitment.handle equalAllocation).trans hhandle)
    exact uncorrected execution executed (congrArg MismatchHandle.stage equalHandle)
  exact ⟨valid, compatible, ⟨allocation, allocMember, hhandle, htool⟩, unused, uncorrected⟩

theorem retained_selected_execute_has_step (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (terminalExecution : C.execution = .terminalBarrier)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order kind r limit seed state.history = .execute handle tool) :
    ∃ next, Step (P.input order) C .uncapped accounting tapes state
      (P.starReferenceRule order kind r limit seed state.history) next := by
  obtain ⟨valid, compatible, backed, unused, uncorrected⟩ := retained_selected_execute_guards P order kind retained r limit
    C .uncapped accounting seed truth tapes path active handle tool selected
  rw [selected]
  refine ⟨_, Step.execute state handle tool active valid compatible backed unused uncorrected ?_ (Or.inl rfl)⟩
  simp only [executionOpen, terminalExecution, reduceCtorEq, false_implies]

end PStarLR
