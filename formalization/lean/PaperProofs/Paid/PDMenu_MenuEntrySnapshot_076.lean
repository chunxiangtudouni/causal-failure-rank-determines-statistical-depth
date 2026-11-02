module

public import PaperProofs.Paid.PDMenu_MenuSettledPast_075

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuPrefix_allCommitmentsExecuted_beforeWrite (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    ∀ a ∈ state.ledger.commitments, ∃ e ∈ state.ledger.executions, e.handle = a.handle ∧ e.tool = a.tool := by
  have hinv := prefix_invariant (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  have hcausal := prefix_cursorInvariant (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  have hsettled := menuPrefix_pastSettled P N K table fee hfee C hC accounting seed truth tapes hp
  intro a ha
  apply hsettled a ha
  have hg := (hinv.commitment_genuine a ha).1
  by_contra hnot
  by_cases hfuture : state.cursor < a.handle.stage.val
  · rw [hcausal.future_written a.handle.stage hfuture] at hg
    cases hg
  · have hs : a.handle.stage = stage := Fin.ext (by omega)
    rw [hs, hopen] at hg
    cases hg

theorem menuPrefix_executions_beforeWrite (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    ∀ e ∈ state.ledger.executions, e.handle.stage.val < state.cursor := by
  have hinv := prefix_invariant (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  have hcausal := prefix_cursorInvariant (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  intro e he
  have hg := (hinv.wellFormed.genuine e he).1
  by_contra hnot
  by_cases hfuture : state.cursor < e.handle.stage.val
  · rw [hcausal.future_written e.handle.stage hfuture] at hg
    cases hg
  · have hs : e.handle.stage = stage := Fin.ext (by omega)
    rw [hs, hopen] at hg
    cases hg

/-- The original table snapshot is exactly the cardinality of genuinely
unused tools before writing a stage. Pending obligations cannot secretly
consume a tool from this state. -/
theorem menuPrefix_entryTools_eq_availableCard (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (stage : (freshInstance N K).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    P.menuEntryTools N K state.history stage = (Finset.univ \ historyUsed state.history).card := by
  classical
  have hwf := prefix_ledgerWellFormed (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  have hsettled := menuPrefix_allCommitmentsExecuted_beforeWrite P N K table fee hfee C hC accounting seed truth tapes hp stage hcursor hopen
  have hbefore := menuPrefix_executions_beforeWrite P N K table fee hfee C accounting seed truth tapes hp stage hcursor hopen
  have hused : historyUsed state.history = (state.ledger.executions.map (·.tool)).toFinset := by
    rw [prefix_historyUsed (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) seed truth tapes hp]
    apply Finset.Subset.antisymm
    · intro tool ht
      obtain ⟨a, ha, hat⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨e, he, _, het⟩ := hsettled a ha
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, het.trans hat⟩)
    · intro tool ht
      obtain ⟨e, he, het⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨a, ha, _, hat, _⟩ := hwf.backed e he
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, hat.trans het⟩)
  have hfiltered : ((state.ledger.executions.map (fun e => (e.handle, e.tool))).filter
      (fun pair => pair.1.stage.val < stage.val)) = state.ledger.executions.map (fun e => (e.handle, e.tool)) := by
    apply List.filter_eq_self.mpr
    intro pair hpairs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpairs
    exact decide_eq_true ((hbefore e he).trans_eq hcursor)
  rw [Parameters.menuEntryTools, prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp, hfiltered, List.length_map, hused,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    List.toFinset_card_of_nodup hwf.execution_tools, List.length_map]
  have hcard : Fintype.card (freshInstance N K).Tool = K := Fintype.card_fin K
  exact congrArg (fun count : ℕ => count - state.ledger.executions.length) hcard.symm

end PDMenu
