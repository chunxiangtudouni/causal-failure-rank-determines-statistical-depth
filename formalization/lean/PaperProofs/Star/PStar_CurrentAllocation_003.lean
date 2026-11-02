module

public import PaperProofs.Star.PStar_CurrentSelection_002
public import PaperProofs.Star.PStarLR_ReportedBarrier_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentAllocation003

open Common Common.Native Parameters PStarLR PStarCurrentChoice001 PStarCurrentSelection002

/-- Every selected allocation of THIS current script has all actual native
guards, including a true versioned report, compatibility, unused stage/tool
and the original current cursor. No successful-path hypothesis is used. -/
theorem current_selected_allocate_guards (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order .current r limit seed state.history = .allocate handle tool) :
    validHandle state handle ∧ tool ∈ (starInstance P.tools order).eligible handle.stage ∧
      (∀ allocation ∈ state.ledger.commitments, allocation.tool ≠ tool) ∧
      (∀ allocation ∈ state.ledger.commitments, allocation.handle.stage ≠ handle.stage) ∧
      state.cursor = handle.stage.val := by
  have correcting : IsCorrection (P.starReferenceRule order .current r limit seed state.history) := by
    rw [selected]
    trivial
  obtain ⟨stage, cursor, wrong, repair⟩ := current_rule_correction_selection P order r limit seed state.history correcting
  obtain ⟨visible, chosen, noCommit, _noExec, hstage⟩ :=
    repairAction_allocate_advance_selection P order state.history stage _ handle tool (repair.symm.trans selected)
  have canonical := prefix_reportedError_genuine (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path stage wrong
  have actualVisible := prefix_referenceVisibleHandle_valid (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path _ canonical
  have valid : validHandle state handle := by
    have heq := Option.some.inj (visible.symm.trans actualVisible)
    rw [heq]
    exact canonical
  have compatible : tool ∈ (starInstance P.tools order).eligible handle.stage := by
    rw [hstage]
    exact currentToolChoice_compatible P order state.history stage tool chosen
  have unused : ∀ allocation ∈ state.ledger.commitments, allocation.tool ≠ tool :=
    (prefix_historyUnused_iff (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes path tool).mp (currentToolChoice_unused P order state.history stage tool chosen)
  have unallocated : ∀ allocation ∈ state.ledger.commitments, allocation.handle.stage ≠ handle.stage := by
    intro allocation member heq
    have visibleMember : (allocation.handle, allocation.tool) ∈ historyCommitments state.history := by
      rw [prefix_historyCommitments (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r limit) seed truth tapes path]
      exact List.mem_map.mpr ⟨allocation, member, rfl⟩
    apply (List.find?_eq_none.mp noCommit) _ visibleMember
    exact beq_iff_eq.mpr (heq.trans hstage)
  refine ⟨valid, compatible, unused, unallocated, ?_⟩
  rw [hstage]
  exact (prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path).symm.trans cursor

theorem current_selected_allocate_has_step (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (active : state.halted = false)
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.starReferenceRule order .current r limit seed state.history = .allocate handle tool) :
    ∃ next, Step (P.input order) C .uncapped accounting tapes state
      (P.starReferenceRule order .current r limit seed state.history) next := by
  obtain ⟨valid, compatible, unused, unallocated, cursor⟩ := current_selected_allocate_guards P order r limit C accounting
    seed truth tapes path handle tool selected
  rw [selected]
  exact ⟨_, Step.allocate state handle tool active valid compatible unused unallocated (fun _ => cursor) (Or.inl rfl)⟩

end PaperProofs.Star.PStarCurrentAllocation003
