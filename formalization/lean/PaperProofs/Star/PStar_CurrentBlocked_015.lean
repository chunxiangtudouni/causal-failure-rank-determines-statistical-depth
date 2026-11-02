module

public import PaperProofs.Star.PStar_CurrentAbort_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentBlocked015

open Common Common.Native Parameters PStarLR PStarCurrentToolIdentity008 PStarCurrentAbort014

theorem commitment_stage_le_cursor {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C mode accounting rule seed truth tapes n state)
    (allocation : Commitment I) (member : allocation ∈ state.ledger.commitments) :
    allocation.handle.stage.val ≤ state.cursor := by
  by_contra beyond
  have future := (prefix_cursorInvariant input C mode accounting rule seed truth tapes path).future_written
    allocation.handle.stage (Nat.lt_of_not_ge beyond)
  have wrong := (prefix_invariant input C mode accounting rule seed truth tapes path).commitment_genuine allocation member
  rw [future] at wrong
  cases wrong.1

/-- A blocked singleton with no current-stage allocation can only be blocked
by the earlier universal allocation. Actual commitments keep their stage
and literal tool identities; no hypothetical matching is used. -/
theorem singletonChoice_none_has_universal (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes n state)
    (stage : (starInstance P.tools order).Stage) (own : Fin P.tools)
    (singleton : stageLabel P.tools order stage = some own)
    (chosen : P.currentToolChoice order state.history stage = none)
    (noCommit : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) = none) :
    ∃ allocation ∈ state.ledger.commitments,
      allocation.handle.stage = universalStage P.tools order ∧ allocation.tool.val = own.val := by
  classical
  have blocked : (historyCommitments state.history).any (fun pair => pair.2.val == own.val) = true := by
    unfold Parameters.currentToolChoice at chosen
    rw [singleton] at chosen
    dsimp only at chosen
    by_contra available
    rw [ite_eq_right available] at chosen
    cases chosen
  obtain ⟨pair, member, equalTool⟩ := List.any_eq_true.mp blocked
  rw [prefix_historyCommitments (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r none) seed truth tapes path] at member
  obtain ⟨allocation, allocated, rfl⟩ := List.mem_map.mp member
  have toolEq : allocation.tool.val = own.val := beq_iff_eq.mp equalTool
  have notCurrent : allocation.handle.stage ≠ stage := by
    intro equalStage
    apply (List.find?_eq_none.mp noCommit) (allocation.handle, allocation.tool)
    · rw [prefix_historyCommitments (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path]
      exact List.mem_map.mpr ⟨allocation, allocated, rfl⟩
    · exact beq_iff_eq.mpr equalStage
  have identity := prefix_allocationToolIdentity P order r none C accounting seed truth tapes path allocation allocated
  cases label : stageLabel P.tools order allocation.handle.stage with
  | none =>
    exact ⟨allocation, allocated, stageLabel_injective P.tools order (label.trans (stageLabel_universal _ _).symm), toolEq⟩
  | some ownLabel =>
    change (match stageLabel P.tools order allocation.handle.stage with
      | some label => allocation.tool.val = label.val
      | none => order = .universalFirst → allocation.tool.val = 0) at identity
    rw [label] at identity
    have sameLabel : ownLabel = own := Fin.ext (identity.symm.trans toolEq)
    exact (notCurrent (stageLabel_injective P.tools order
      (label.trans ((congrArg some sameLabel).trans singleton.symm)))).elim

theorem universalFirst_abandon_two_errors (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .universalFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .universalFirst)) {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) seed truth tapes n state)
    (active : state.halted = false)
    (selected : P.starReferenceRule .universalFirst .current r none seed state.history = .abandon) :
    state.ledger.written (universalStage P.tools .universalFirst) =
      some (!state.ledger.truth (universalStage P.tools .universalFirst)) ∧
    state.ledger.written (singletonStage P.tools .universalFirst P.firstTool) =
      some (!state.ledger.truth (singletonStage P.tools .universalFirst P.firstTool)) := by
  obtain ⟨stage, cursor, wrong, chosen, noCommit⟩ :=
    current_abandon_selection P .universalFirst r C early accounting seed truth tapes path active selected
  cases label : stageLabel P.tools .universalFirst stage with
  | some own =>
    obtain ⟨allocation, member, universal, toolEq⟩ := singletonChoice_none_has_universal
      P .universalFirst r C accounting seed truth tapes path stage own label chosen noCommit
    have identity := prefix_allocationToolIdentity P .universalFirst r none C accounting
      seed truth tapes path allocation member
    unfold ToolIdentity at identity
    rw [universal, stageLabel_universal] at identity
    have zero : own = P.firstTool := Fin.ext (toolEq.symm.trans (identity rfl))
    have singleton : stage = singletonStage P.tools .universalFirst P.firstTool :=
      stageLabel_injective P.tools .universalFirst
        (label.trans ((congrArg some zero).trans (stageLabel_singleton _ _ _).symm))
    have headWrong := (prefix_invariant (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) seed truth tapes path).commitment_genuine allocation member
    rw [universal] at headWrong
    exact ⟨headWrong.1, singleton ▸ wrong⟩
  | none =>
    have universal : stage = universalStage P.tools .universalFirst :=
      stageLabel_injective P.tools .universalFirst (label.trans (stageLabel_universal _ _).symm)
    have zero : state.cursor = 0 := cursor.trans (by rw [universal]; rfl)
    unfold Parameters.currentToolChoice at chosen
    rw [label] at chosen
    dsimp only at chosen
    have blocked : (historyCommitments state.history).any (fun pair => pair.2.val == 0) = true := by
      by_contra free
      rw [ite_eq_right free] at chosen
      cases chosen
    obtain ⟨pair, member, _tool⟩ := List.any_eq_true.mp blocked
    rw [prefix_historyCommitments (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) seed truth tapes path] at member
    obtain ⟨allocation, allocated, rfl⟩ := List.mem_map.mp member
    have bound := commitment_stage_le_cursor (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) seed truth tapes path allocation allocated
    have equalStage : allocation.handle.stage = stage := by
      apply Fin.ext
      rw [zero] at bound
      omega
    apply False.elim
    apply (List.find?_eq_none.mp noCommit) (allocation.handle, allocation.tool)
    · rw [prefix_historyCommitments (P.input .universalFirst) C .uncapped accounting
        (P.starReferenceRule .universalFirst .current r none) seed truth tapes path]
      exact List.mem_map.mpr ⟨allocation, allocated, rfl⟩
    · exact beq_iff_eq.mpr equalStage

end PaperProofs.Star.PStarCurrentBlocked015
