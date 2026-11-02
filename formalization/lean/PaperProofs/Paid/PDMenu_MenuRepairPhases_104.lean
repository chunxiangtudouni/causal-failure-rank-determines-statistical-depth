module

public import PaperProofs.Paid.PDMenu_MenuFreshRepair_102
public import PaperProofs.Paid.PDMenu_MenuNativeActionRun_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

theorem menuPrefix_no_current_execution (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {clock : ℕ} {state : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes clock state) (stage : I.Stage)
    (hnocommit : ∀ commitment ∈ state.ledger.commitments, commitment.handle.stage ≠ stage) :
    ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ stage := by
  have hwf := prefix_ledgerWellFormed input C .uncapped accounting rule seed truth tapes hp
  intro execution he hs
  obtain ⟨commitment, hc, hh, _, _⟩ := hwf.backed execution he
  exact hnocommit commitment hc ((congrArg MismatchHandle.stage hh).trans hs)

/-- The visible first matching commitment is the actual unique commitment
for this stage, including its physical tool and original write serial. -/
theorem menuPrefix_find_current_commitment (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {clock : ℕ} {state : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes clock state)
    (stage : I.Stage) (commitment : Commitment I) (hc : commitment ∈ state.ledger.commitments)
    (hs : commitment.handle.stage = stage) :
    (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) =
      some (commitment.handle, commitment.tool) := by
  classical
  have hm : (commitment.handle, commitment.tool) ∈ historyCommitments state.history := by
    rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp]
    exact List.mem_map.mpr ⟨commitment, hc, rfl⟩
  cases hfind : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) with
  | none =>
    have hnot := List.find?_eq_none.mp hfind (commitment.handle, commitment.tool) hm
    exact (hnot (by simp only [hs, beq_self_eq_true])).elim
  | some pair =>
    have hpairs := List.mem_of_find?_eq_some hfind
    have hstage : pair.1.stage = stage := by simpa only [beq_iff_eq] using List.find?_some hfind
    rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp] at hpairs
    obtain ⟨selected, hselected, heq⟩ := List.mem_map.mp hpairs
    have hsame : selected.handle.stage = commitment.handle.stage :=
      (congrArg (fun pair : MismatchHandle I × I.Tool => pair.1.stage) heq).trans (hstage.trans hs.symm)
    have hwf := prefix_ledgerWellFormed input C .uncapped accounting rule seed truth tapes hp
    have he : selected = commitment := List.inj_on_of_nodup_map hwf.commitment_stages hselected hc hsame
    subst selected
    exact congrArg some heq.symm

theorem compiledMenuRule_allocated_repair_executes (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K state.history stage)).action = .test level .repair)
    (commitment : Commitment (freshInstance N K)) (hc : commitment ∈ state.ledger.commitments)
    (hs : commitment.handle.stage = stage)
    (hnoexec : ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ stage) :
    P.compiledMenuRule N K table menuSeed state.history = .execute commitment.handle commitment.tool := by
  have hdone : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
    apply Bool.eq_false_iff.mpr
    intro hsome
    obtain ⟨pair, hm, hstage⟩ := List.any_eq_true.mp hsome
    rw [prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp] at hm
    obtain ⟨execution, he, heq⟩ := List.mem_map.mp hm
    have heStage : execution.handle.stage = pair.1.stage :=
      congrArg (fun pair : MismatchHandle (freshInstance N K) × (freshInstance N K).Tool => pair.1.stage) heq
    exact hnoexec execution he (heStage.trans (by simpa only [beq_iff_eq] using hstage))
  rw [compiledMenuRule_written_wrong P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit hwrong, hcell]
  simp only [Parameters.menuRepairAction, hdone, Bool.false_eq_true, ite_false,
    menuPrefix_find_current_commitment (P.freshInput N K fee hfee) C accounting rule seed truth tapes hp stage commitment hc hs]

theorem compiledMenuRule_executed_repair_advances (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K state.history stage)).action = .test level .repair)
    (execution : Execution (freshInstance N K)) (he : execution ∈ state.ledger.executions)
    (hs : execution.handle.stage = stage) :
    P.compiledMenuRule N K table menuSeed state.history = .advance stage := by
  have hdone : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = true := by
    apply List.any_eq_true.mpr
    refine ⟨(execution.handle, execution.tool), ?_, ?_⟩
    · rw [prefix_historyExecutions (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨execution, he, rfl⟩
    · simp only [hs, beq_self_eq_true]
  rw [compiledMenuRule_written_wrong P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit hwrong, hcell]
  exact ite_eq_left hdone

end PDMenu
