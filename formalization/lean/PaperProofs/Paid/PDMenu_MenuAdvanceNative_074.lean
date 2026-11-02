module

public import PaperProofs.Paid.PDMenu_MenuAdvanceShape_073
public import PaperProofs.Paid.PDMenu_MenuGuard_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The actual compiled script advances only after a correct ordinary
answer or a real execution at that stage, on every reached prefix. -/
theorem menuPrefix_advance_good_or_executed (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) {Seed : Type*}
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage)
    (ha : P.compiledMenuRule N K table menuSeed state.history = .advance stage) :
    state.ledger.written stage = some (state.ledger.truth stage) ∨
      ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage := by
  rw [compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hearly accounting rule seed truth tapes hp menuSeed] at ha
  rcases menuCandidateAction_advance_spec P N K table menuSeed state.history stage ha with hcorrect | hexecuted
  · obtain ⟨bit, serial, hw, hr⟩ := hcorrect
    rw [prefix_historyWritten (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp stage] at hw
    rw [prefix_historyReport_early (P.freshInput N K fee hfee) C hearly .uncapped accounting rule seed truth tapes hp stage] at hr
    cases ht : state.ledger.reportTime stage with
    | none => simp only [ht, Option.map_none, reduceCtorEq] at hr
    | some time =>
      simp only [ht, Option.map_some, Option.some.injEq] at hr
      exact Or.inl (hw.trans (congrArg some (congrArg Prod.fst hr).symm))
  · obtain ⟨pair, hpairs, hs⟩ := hexecuted
    rw [prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hpairs
    obtain ⟨execution, he, heq⟩ := List.mem_map.mp hpairs
    exact Or.inr ⟨execution, he, (congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq).trans hs⟩

end PDMenu
