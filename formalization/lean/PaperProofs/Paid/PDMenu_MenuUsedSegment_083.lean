module

public import PaperProofs.Paid.PDMenu_MenuAllocationChoice_082
public import PaperProofs.Paid.PDMenu_MenuUnusedTool_081
public import PaperProofs.Paid.PDMenu_MenuGuard_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def MenuUsedInitial {I : Instance} (ledger : Ledger I) : Prop :=
  ∀ tool : I.Tool, tool ∈ (ledger.commitments.map (·.tool)).toFinset ↔ tool.val < ledger.commitments.length

/-- Actual allocations of the literal compiler use original tools in
ascending order. The statement includes a current pending allocation. -/
theorem menuPrefix_usedInitial (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state) : MenuUsedInitial state.ledger := by
  classical
  induction hp with
  | initial =>
    intro tool
    simp [initial]
  | @next clock state nextState hp hstep ih =>
    generalize haction : P.compiledMenuRule N K table seed state.history = action at hstep
    cases hstep with
    | review => exact ih
    | write stage bit live port resources =>
      simpa only [MenuUsedInitial, record, reportedWriteLedger, hC.1.1, ite_true, writeLedger] using ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have hcand : P.menuCandidateAction N K table seed state.history = .allocate handle tool :=
        (compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hC.1.1 accounting
          (P.compiledMenuRule N K table) seed truth tapes hp seed).symm.trans haction
      have hchoice := menuCandidateAction_allocate_choice P N K table seed state.history handle tool hcand
      have hused : ∀ selected : (freshInstance N K).Tool,
          selected ∈ historyUsed state.history ↔ selected.val < state.ledger.commitments.length := by
        intro selected
        rw [prefix_historyUsed (P.freshInput N K fee hfee) C .uncapped accounting
          (P.compiledMenuRule N K table) seed truth tapes hp]
        exact ih selected
      have hval := menuUnusedTool_val_of_initial_segment P N K state.ledger.commitments.length state.history hused tool hchoice
      intro selected
      have hold : selected ∈ state.ledger.commitments.map (·.tool) ↔ selected.val < state.ledger.commitments.length :=
        List.mem_toFinset.symm.trans (ih selected)
      have heq : selected = tool ↔ selected.val = state.ledger.commitments.length := by
        constructor
        · intro he
          exact (congrArg Fin.val he).trans hval
        · intro he
          exact Fin.ext (he.trans hval.symm)
      let newCommit : Commitment (freshInstance N K) := ⟨handle, tool, state.clock⟩
      change selected ∈ ((state.ledger.commitments ++ [newCommit]).map (fun a : Commitment (freshInstance N K) => a.tool)).toFinset ↔
        selected.val < (state.ledger.commitments ++ [newCommit]).length
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_toFinset, List.mem_append,
        List.mem_singleton, List.length_append, List.length_singleton]
      rw [hold, heq]
      omega
    | execute | advance | stop | abandon => exact ih

theorem menuPrefix_historyUsed_initial_segment (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state) :
    ∀ tool : (freshInstance N K).Tool,
      tool ∈ historyUsed state.history ↔ tool.val < state.ledger.commitments.length := by
  intro tool
  rw [prefix_historyUsed (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp]
  exact menuPrefix_usedInitial P N K table fee hfee C hC accounting seed truth tapes hp tool

end PDMenu
