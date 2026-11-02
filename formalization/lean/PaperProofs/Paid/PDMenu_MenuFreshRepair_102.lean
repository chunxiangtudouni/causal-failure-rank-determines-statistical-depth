module

public import PaperProofs.Paid.PDMenu_MenuWrittenFrame_097
public import PaperProofs.Paid.PDMenu_MenuUnusedTool_081

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- On the real freshly written wrong branch, the literal compiler chooses
an actual unused physical tool and allocates the actual visible serial.
No continuation policy or expected-performance assertion is an input. -/
theorem compiledMenuRule_fresh_repair_allocates (P : Parameters) (N K : ℕ) (table : MenuTable)
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
    (havailable : 0 < (Finset.univ \ historyUsed state.history).card) :
    ∃ tool, P.menuUnusedTool N K state.history = some tool ∧
      P.compiledMenuRule N K table menuSeed state.history =
        .allocate ⟨stage, state.ledger.writeSerial stage⟩ tool := by
  classical
  have hwf := prefix_ledgerWellFormed (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp
  have hncommit : ∀ pair ∈ historyCommitments state.history, pair.1.stage ≠ stage := by
    intro pair hm
    rw [prefix_historyCommitments (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hm
    obtain ⟨commitment, hc, heq⟩ := List.mem_map.mp hm
    have hstage : commitment.handle.stage = pair.1.stage :=
      congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq
    exact fun hs => hnoCurrent commitment hc (hstage.trans hs)
  have hnexec : ∀ pair ∈ historyExecutions state.history, pair.1.stage ≠ stage := by
    intro pair hm
    rw [prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hm
    obtain ⟨execution, he, heq⟩ := List.mem_map.mp hm
    obtain ⟨commitment, hc, hh, _, _⟩ := hwf.backed execution he
    have hstage : execution.handle.stage = pair.1.stage :=
      congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq
    exact fun hs => hnoCurrent commitment hc ((congrArg MismatchHandle.stage hh).trans (hstage.trans hs))
  have hdone : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
    apply Bool.eq_false_iff.mpr
    intro hsome
    obtain ⟨pair, hm, hs⟩ := List.any_eq_true.mp hsome
    exact hnexec pair hm (by simpa only [beq_iff_eq] using hs)
  have hfind : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) = none := by
    apply List.find?_eq_none.mpr
    intro pair hm
    simpa only [beq_iff_eq] using hncommit pair hm
  have hvisible : referenceVisibleHandle state.history stage = some ⟨stage, state.ledger.writeSerial stage⟩ := by
    rw [referenceVisibleHandle,
      prefix_historyWrite (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp stage, hbit]
    rfl
  obtain ⟨tool, htool⟩ := menuUnusedTool_exists_of_available P N K state.history havailable
  refine ⟨tool, htool, ?_⟩
  rw [compiledMenuRule_written_wrong P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit hwrong, hcell]
  simp only [Parameters.menuRepairAction, hdone, Bool.false_eq_true, ite_false, hfind, hvisible, htool]

end PDMenu
