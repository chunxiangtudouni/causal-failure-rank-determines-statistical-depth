module

public import PaperProofs.Paid.PDMenu_MenuUsedSegment_083
public import PaperProofs.Paid.PDMenu_MenuEntrySnapshot_076

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuPrefix_commitmentCount_eq_executionCount_beforeWrite (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    state.ledger.commitments.length = state.ledger.executions.length := by
  classical
  have hwf := prefix_ledgerWellFormed (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  have hsettled := menuPrefix_allCommitmentsExecuted_beforeWrite P N K table fee hfee C hC accounting seed truth tapes hp stage hcursor hopen
  have hset : (state.ledger.commitments.map (·.tool)).toFinset = (state.ledger.executions.map (·.tool)).toFinset := by
    apply Finset.Subset.antisymm
    · intro tool ht
      obtain ⟨a, ha, hat⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨e, he, _, het⟩ := hsettled a ha
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, het.trans hat⟩)
    · intro tool ht
      obtain ⟨e, he, het⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨a, ha, _, hat, _⟩ := hwf.backed e he
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, hat.trans het⟩)
  have hc := congrArg Finset.card hset
  simpa only [List.toFinset_card_of_nodup hwf.commitment_tools,
    List.toFinset_card_of_nodup hwf.execution_tools, List.length_map] using hc

/-- Before the current write, exactly the original physically spent tool
prefix is unavailable. No pending obligation is silently discarded. -/
theorem menuPrefix_used_physical_initial_segment (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    ∀ tool : (freshInstance N K).Tool,
      tool ∈ historyUsed state.history ↔ tool.val < state.ledger.executions.length := by
  intro tool
  rw [menuPrefix_historyUsed_initial_segment P N K table fee hfee C hC accounting seed truth tapes hp,
    menuPrefix_commitmentCount_eq_executionCount_beforeWrite P N K table fee hfee C hC accounting seed truth tapes hp stage hcursor hopen]

theorem menuPrefix_entryTools_eq_physical_sub (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    P.menuEntryTools N K state.history stage = K - state.ledger.executions.length := by
  have hbefore := menuPrefix_executions_beforeWrite P N K table fee hfee C accounting seed truth tapes hp stage hcursor hopen
  have hfiltered : ((state.ledger.executions.map (fun e => (e.handle, e.tool))).filter
      (fun pair => pair.1.stage.val < stage.val)) = state.ledger.executions.map (fun e => (e.handle, e.tool)) := by
    apply List.filter_eq_self.mpr
    intro pair hpairs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpairs
    exact decide_eq_true ((hbefore e he).trans_eq hcursor)
  rw [Parameters.menuEntryTools, prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp, hfiltered, List.length_map]

end PDMenu
