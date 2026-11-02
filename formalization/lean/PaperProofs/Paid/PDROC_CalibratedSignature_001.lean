module

public import PaperProofs.Common.NativeRepairCount

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native
open scoped ENNReal

namespace PDROC.CalibratedSignature

variable {I : Instance} {Seed : Type*}

def ledgerExecutedTools (L : Ledger I) : Finset I.Tool :=
  (L.executions.map (fun execution => execution.tool)).toFinset

theorem ledgerExecutedTools_card (L : Ledger I) (wellFormed : LedgerWellFormed L) :
    (ledgerExecutedTools L).card = L.executions.length := by
  simpa only [ledgerExecutedTools, List.length_map] using
    List.toFinset_card_of_nodup wellFormed.execution_tools

theorem step_executedTools_subset (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next) :
    ledgerExecutedTools state.ledger ⊆ ledgerExecutedTools next.ledger := by
  classical
  cases step with
  | write =>
    simp only [ledgerExecutedTools, record, reportedWriteLedger]
    split_ifs <;> exact Finset.Subset.rfl
  | execute =>
    change (state.ledger.executions.map (fun execution => execution.tool)).toFinset ⊆
      ((state.ledger.executions ++ [_]).map (fun execution : Execution I => execution.tool)).toFinset
    rw [List.map_append, List.toFinset_append]
    exact Finset.subset_union_left
  | review | allocate | advance | stop | abandon => exact Finset.Subset.rfl

theorem run_executedTools_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    Monotone (fun clock => ledgerExecutedTools (run input C mode accounting rule sample clock).ledger) := by
  apply monotone_nat_of_le_succ
  intro clock
  by_cases halted : (run input C mode accounting rule sample clock).halted = true
  · rw [run_succ_of_halted input C mode accounting rule sample clock halted]
  · have active : (run input C mode accounting rule sample clock).halted = false := Bool.eq_false_iff.mpr halted
    obtain ⟨n, _before, path⟩ := run_has_prefix input C mode accounting rule legal sample clock
    obtain ⟨next, step⟩ := legal sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      n _ path active
    rw [run_succ_of_step input C mode accounting rule sample clock next active step]
    exact step_executedTools_subset input C mode accounting _ step

/-- Every physical tool ever executed on the actual path. This retains
executions before eventual failure or nonreturn and does not require a halt. -/
noncomputable def everExecutedTools (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) : Finset I.Tool := by
  classical
  exact Finset.univ.filter (fun tool => ∃ clock,
    tool ∈ ledgerExecutedTools (run input C mode accounting rule sample clock).ledger)

theorem mem_everExecutedTools (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (tool : I.Tool) :
    tool ∈ everExecutedTools input C mode accounting rule sample ↔
      ∃ clock, tool ∈ ledgerExecutedTools (run input C mode accounting rule sample clock).ledger := by
  classical
  simp only [everExecutedTools, Finset.mem_filter, Finset.mem_univ, true_and]

theorem run_executedTools_subset_ever (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (clock : ℕ) :
    ledgerExecutedTools (run input C mode accounting rule sample clock).ledger ⊆
      everExecutedTools input C mode accounting rule sample := by
  intro tool member
  exact (mem_everExecutedTools input C mode accounting rule sample tool).mpr ⟨clock, member⟩

/-- Finitely many physical tools give one actual clock containing every
ever-executed tool, even when the run itself never halts. -/
theorem exists_clock_executedTools_eq_ever (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    ∃ clock, ledgerExecutedTools (run input C mode accounting rule sample clock).ledger =
      everExecutedTools input C mode accounting rule sample := by
  classical
  let witness : I.Tool → ℕ := fun tool =>
    if present : ∃ clock, tool ∈ ledgerExecutedTools (run input C mode accounting rule sample clock).ledger then
      Classical.choose present else 0
  let clock := Finset.univ.sup witness
  refine ⟨clock, Finset.Subset.antisymm (run_executedTools_subset_ever input C mode accounting rule sample clock) ?_⟩
  intro tool member
  have present := (mem_everExecutedTools input C mode accounting rule sample tool).mp member
  have witnessed : tool ∈ ledgerExecutedTools (run input C mode accounting rule sample (witness tool)).ledger := by
    dsimp only [witness]
    rw [dite_eq_left present]
    exact Classical.choose_spec present
  exact run_executedTools_mono input C mode accounting rule legal sample
    (Finset.le_sup (Finset.mem_univ tool)) witnessed

theorem runRepairCount_eq_everExecutedTools_card (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    runRepairCount input C mode accounting rule sample =
      ((everExecutedTools input C mode accounting rule sample).card : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro clock
    have cards := Finset.card_le_card (run_executedTools_subset_ever input C mode accounting rule sample clock)
    rw [ledgerExecutedTools_card _ (run_ledgerWellFormed input C mode accounting rule legal sample clock)] at cards
    exact_mod_cast cards
  · obtain ⟨clock, same⟩ := exists_clock_executedTools_eq_ever input C mode accounting rule legal sample
    have cards : (run input C mode accounting rule sample clock).ledger.executions.length =
        (everExecutedTools input C mode accounting rule sample).card := by
      rw [← ledgerExecutedTools_card _ (run_ledgerWellFormed input C mode accounting rule legal sample clock), same]
    rw [← cards]
    exact le_iSup (fun clock => ((run input C mode accounting rule sample clock).ledger.executions.length : ℝ≥0∞)) clock

end PDROC.CalibratedSignature
