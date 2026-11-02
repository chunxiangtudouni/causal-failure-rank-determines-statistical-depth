module

public import PaperProofs.Paid.PDMenu_MenuHistoryPermissions_066

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- All branches of the literal greedy repair routine pass the visible
permission check on a real prefix. No numerical table invariant is used. -/
theorem menuRepairAction_allowed (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting (freshInstance N K))
    {Seed : Type*} (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C mode accounting rule seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : historyCursor state.history = stage.val)
    (hw : historyWritten state.history stage ≠ none)
    (hvisible : ∀ handle, referenceVisibleHandle state.history stage = some handle →
      handle.stage = stage ∧ historyValidHandle state.history handle) :
    historyAllowsAction state.history (P.menuRepairAction N K state.history stage) := by
  classical
  by_cases hdone : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = true
  · simp only [Parameters.menuRepairAction, hdone, ite_true, historyAllowsAction]
    exact ⟨hcursor, hw⟩
  · have hnexec : ∀ pair ∈ historyExecutions state.history, pair.1.stage ≠ stage := by
      intro pair hpair hstage
      exact hdone (List.any_eq_true.mpr ⟨pair, hpair, by simpa only [beq_iff_eq] using hstage⟩)
    simp only [Parameters.menuRepairAction, hdone]
    cases hc : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) with
    | some pair =>
      have hm := List.mem_of_find?_eq_some hc
      have hs : pair.1.stage = stage := by simpa only [beq_iff_eq] using List.find?_some hc
      have hv := menuCommittedHandle_valid (P.freshInput N K fee hfee) C hearly mode accounting rule seed truth tapes hp pair hm
      refine ⟨hcursor.trans (congrArg Fin.val hs).symm, hv, by
        simp [freshInstance, Instance.eligible]
        exact Finset.mem_univ _, hm, ?_, ?_⟩
      · intro executed he htool
        exact hnexec executed he ((menuExecutedTool_stage (P.freshInput N K fee hfee) C mode accounting
          rule seed truth tapes hp pair executed hm he htool).trans hs)
      · intro executed he
        exact (hnexec executed he).trans_eq hs.symm
    | none =>
      have hncommit : ∀ pair ∈ historyCommitments state.history, pair.1.stage ≠ stage := by
        intro pair hm
        simpa only [beq_iff_eq] using List.find?_eq_none.mp hc pair hm
      cases hh : referenceVisibleHandle state.history stage with
      | none => trivial
      | some handle =>
        cases ht : P.menuUnusedTool N K state.history with
        | none => trivial
        | some tool =>
          obtain ⟨hs, hv⟩ := hvisible handle hh
          have hu : tool ∉ historyUsed state.history := by
            simpa only [decide_eq_true_eq] using List.find?_some ht
          refine ⟨hcursor.trans (congrArg Fin.val hs).symm, hv, by
            simp [freshInstance, Instance.eligible]
            exact Finset.mem_univ _, hu, ?_⟩
          intro pair hm
          exact (hncommit pair hm).trans_eq hs.symm

end PDMenu
