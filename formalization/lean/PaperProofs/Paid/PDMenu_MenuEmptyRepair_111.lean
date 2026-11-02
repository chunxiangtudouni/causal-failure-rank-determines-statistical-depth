module

public import PaperProofs.Paid.PDMenu_MenuRepairPhases_104

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuUnusedTool_none_of_available_zero (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K)))
    (hzero : (Finset.univ \ historyUsed history).card = 0) :
    P.menuUnusedTool N K history = none := by
  classical
  cases hfind : P.menuUnusedTool N K history with
  | none => rfl
  | some tool =>
    have hunused : tool ∉ historyUsed history := by
      simpa only [decide_eq_true_eq] using List.find?_some hfind
    have hpos : 0 < (Finset.univ \ historyUsed history).card :=
      Finset.card_pos.mpr ⟨tool, Finset.mem_sdiff.mpr ⟨Finset.mem_univ tool, hunused⟩⟩
    omega

theorem compiledMenuRule_fresh_repair_no_tool (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) {Seed : Type*}
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K state.history stage)).action = .test level .repair)
    (hnoCurrent : ∀ commitment ∈ state.ledger.commitments, commitment.handle.stage ≠ stage)
    (havailable : (Finset.univ \ historyUsed state.history).card = 0) :
    P.compiledMenuRule N K table menuSeed state.history = .abandon := by
  have hnoexec := menuPrefix_no_current_execution (P.freshInput N K fee hfee) C accounting rule seed truth tapes hp stage hnoCurrent
  have hdone : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
    apply Bool.eq_false_iff.mpr
    intro hsome
    obtain ⟨pair, hm, hs⟩ := List.any_eq_true.mp hsome
    rw [prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hm
    obtain ⟨execution, he, heq⟩ := List.mem_map.mp hm
    have hstage : execution.handle.stage = pair.1.stage :=
      congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq
    exact hnoexec execution he (hstage.trans (by simpa only [beq_iff_eq] using hs))
  have hfind : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) = none := by
    apply List.find?_eq_none.mpr
    intro pair hm hs
    rw [prefix_historyCommitments (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hm
    obtain ⟨commitment, hc, heq⟩ := List.mem_map.mp hm
    have hstage : commitment.handle.stage = pair.1.stage :=
      congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq
    exact hnoCurrent commitment hc (hstage.trans (by simpa only [beq_iff_eq] using hs))
  rw [compiledMenuRule_written_wrong P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit hwrong, hcell]
  simp only [Parameters.menuRepairAction, hdone, Bool.false_eq_true, ite_false, hfind,
    menuUnusedTool_none_of_available_zero P N K state.history havailable]
  cases referenceVisibleHandle state.history stage <;> rfl

end PDMenu
