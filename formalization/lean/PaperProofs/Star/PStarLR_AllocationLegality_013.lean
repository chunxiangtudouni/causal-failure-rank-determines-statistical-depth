module

public import PaperProofs.Star.PStarLR_AllocationInvariant_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem retained_selected_allocate_guards (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order kind r limit seed state.history = .allocate handle tool) :
    validHandle state handle ∧ tool ∈ (starInstance P.tools order).eligible handle.stage ∧
      (∀ allocation ∈ state.ledger.commitments, allocation.tool ≠ tool) ∧
      (∀ allocation ∈ state.ledger.commitments, allocation.handle.stage ≠ handle.stage) := by
  classical
  have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
    rw [selected]
    trivial
  have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans active
  have barrier := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive terminal
  obtain ⟨stage, _size, wrong, visible, chosen, noCommit, _noExec, hstage⟩ :=
    barrierAction_allocate_selection P order state.history handle tool (barrier.symm.trans selected)
  have canonicalValid := prefix_reportedError_genuine (P.input order) C mode accounting
    (P.starReferenceRule order kind r limit) seed truth tapes path stage wrong
  have canonicalVisible := prefix_referenceVisibleHandle_valid (P.input order) C mode accounting
    (P.starReferenceRule order kind r limit) seed truth tapes path _ canonicalValid
  have valid : validHandle state handle := by
    have heq := Option.some.inj (visible.symm.trans canonicalVisible)
    rw [heq]
    exact canonicalValid
  have unallocated : ∀ allocation ∈ state.ledger.commitments, allocation.handle.stage ≠ handle.stage := by
    intro allocation member heq
    have visibleMember : (allocation.handle, allocation.tool) ∈ historyCommitments state.history := by
      rw [prefix_historyCommitments (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
        seed truth tapes path]
      exact List.mem_map.mpr ⟨allocation, member, rfl⟩
    apply (List.find?_eq_none.mp noCommit) _ visibleMember
    exact beq_iff_eq.mpr (heq.trans hstage)
  have unused : ∀ allocation ∈ state.ledger.commitments, allocation.tool ≠ tool := by
    intro allocation member heq
    obtain ⟨oldWrong, oldChoice⟩ := prefix_allocationChoices P order kind retained r limit C mode accounting
      seed truth tapes path allocation member
    have oldChoice' : P.retainedToolChoice order state.history allocation.handle.stage = some tool := by
      rw [← heq]
      exact oldChoice
    have sameStage := retainedToolChoice_injective_on_errors P order state.history allocation.handle.stage
      stage tool oldWrong wrong oldChoice' chosen
    exact unallocated allocation member (sameStage.trans hstage.symm)
  refine ⟨valid, ?_, unused, unallocated⟩
  rw [hstage]
  exact retainedToolChoice_compatible P order state.history stage tool chosen

theorem retained_selected_allocate_has_step (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order kind r limit seed state.history = .allocate handle tool) :
    ∃ next, Step (P.input order) C .uncapped accounting tapes state
      (P.starReferenceRule order kind r limit seed state.history) next := by
  obtain ⟨valid, compatible, unused, unallocated⟩ := retained_selected_allocate_guards P order kind retained r limit
    C .uncapped accounting seed truth tapes path active handle tool selected
  rw [selected]
  refine ⟨_, Step.allocate state handle tool active valid compatible unused unallocated ?_ (Or.inl rfl)⟩
  simp only [allocationOpen, terminalAllocation, reduceCtorEq, false_implies]

end PStarLR
