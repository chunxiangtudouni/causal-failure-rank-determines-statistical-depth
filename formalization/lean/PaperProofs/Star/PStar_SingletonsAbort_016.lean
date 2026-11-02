module

public import PaperProofs.Star.PStar_CurrentBlocked_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarSingletonsAbort016

open Common Common.Native Parameters PStarLR PStarCurrentToolIdentity008
  PStarCurrentAbort014 PStarCurrentBlocked015

/-- The original singleton-first current controller cannot abandon at a
singleton. At its actual universal-stage abandon EVERY ordinary bit is a
true error, including the final bit. -/
theorem singletonsFirst_abandon_all_errors (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .singletonsFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .singletonsFirst)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools .singletonsFirst).Stage → Bool)
    (tapes : ReviewTapes (P.input .singletonsFirst)) {n : ℕ} {state : State (starInstance P.tools .singletonsFirst)}
    (path : Prefix (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes n state)
    (active : state.halted = false)
    (selected : P.starReferenceRule .singletonsFirst .current r none seed state.history = .abandon) :
    ∀ stage : (starInstance P.tools .singletonsFirst).Stage,
      state.ledger.written stage = some (!state.ledger.truth stage) := by
  classical
  obtain ⟨current, cursor, wrong, chosen, noCommit⟩ :=
    current_abandon_selection P .singletonsFirst r C early accounting seed truth tapes path active selected
  have actualWrong (allocation : Commitment (starInstance P.tools .singletonsFirst))
      (member : allocation ∈ state.ledger.commitments) :
      state.ledger.written allocation.handle.stage = some (!state.ledger.truth allocation.handle.stage) :=
    ((prefix_invariant (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path).commitment_genuine allocation member).1
  have notCurrent (allocation : Commitment (starInstance P.tools .singletonsFirst))
      (member : allocation ∈ state.ledger.commitments) : allocation.handle.stage ≠ current := by
    intro equalStage
    apply (List.find?_eq_none.mp noCommit) (allocation.handle, allocation.tool)
    · rw [prefix_historyCommitments (P.input .singletonsFirst) C .uncapped accounting
        (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path]
      exact List.mem_map.mpr ⟨allocation, member, rfl⟩
    · exact beq_iff_eq.mpr equalStage
  cases currentLabel : stageLabel P.tools .singletonsFirst current with
  | some own =>
    obtain ⟨allocation, member, universal, _tool⟩ := singletonChoice_none_has_universal
      P .singletonsFirst r C accounting seed truth tapes path current own currentLabel chosen noCommit
    have bound := commitment_stage_le_cursor (P.input .singletonsFirst) C .uncapped accounting
      (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path allocation member
    have currentStage : current = singletonStage P.tools .singletonsFirst own :=
      stageLabel_injective P.tools .singletonsFirst (currentLabel.trans (stageLabel_singleton _ _ _).symm)
    have universalVal : allocation.handle.stage.val = P.tools := by rw [universal]; rfl
    have singletonVal : current.val = own.val := by rw [currentStage]; rfl
    have ownBound := own.isLt
    omega
  | none =>
    have everyTool (tool : Fin P.tools) :
        (historyCommitments state.history).any (fun pair => pair.2.val == tool.val) = true := by
      by_contra free
      have unused : tool ∈ (Finset.univ.filter fun candidate : Fin P.tools =>
          !(historyCommitments state.history).any (fun pair => pair.2.val == candidate.val)) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Bool.eq_false_iff.mpr free]; rfl⟩
      obtain ⟨available, found, _member⟩ := firstOfFinset_exists _ ⟨tool, unused⟩
      change @Eq (Option (Fin P.tools)) (P.currentToolChoice .singletonsFirst state.history current) none at chosen
      unfold Parameters.currentToolChoice at chosen
      rw [currentLabel] at chosen
      dsimp only at chosen
      have impossible : (none : Option (Fin P.tools)) = some available := chosen.symm.trans found
      cases impossible
    intro stage
    by_cases currentStage : stage = current
    · subst stage
      exact wrong
    · cases label : stageLabel P.tools .singletonsFirst stage with
      | none => exact (currentStage (stageLabel_injective P.tools .singletonsFirst (label.trans currentLabel.symm))).elim
      | some own =>
        obtain ⟨pair, member, htool⟩ := List.any_eq_true.mp (everyTool own)
        rw [prefix_historyCommitments (P.input .singletonsFirst) C .uncapped accounting
          (P.starReferenceRule .singletonsFirst .current r none) seed truth tapes path] at member
        obtain ⟨allocation, allocated, rfl⟩ := List.mem_map.mp member
        have toolEq : allocation.tool.val = own.val := beq_iff_eq.mp htool
        have identity := prefix_allocationToolIdentity P .singletonsFirst r none C accounting
          seed truth tapes path allocation allocated
        cases allocationLabel : stageLabel P.tools .singletonsFirst allocation.handle.stage with
        | none =>
          exact (notCurrent allocation allocated (stageLabel_injective P.tools .singletonsFirst
            (allocationLabel.trans currentLabel.symm))).elim
        | some ownAllocation =>
          unfold ToolIdentity at identity
          rw [allocationLabel] at identity
          have sameTool : ownAllocation = own := Fin.ext (identity.symm.trans toolEq)
          have sameStage : allocation.handle.stage = stage := stageLabel_injective P.tools .singletonsFirst
            (allocationLabel.trans ((congrArg some sameTool).trans label.symm))
          rw [← sameStage]
          exact actualWrong allocation allocated

end PaperProofs.Star.PStarSingletonsAbort016
