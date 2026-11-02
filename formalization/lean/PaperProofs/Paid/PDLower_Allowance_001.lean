module

public import PaperProofs.Paid.PDLower_Survival_002
public import PaperProofs.Paid.PDROC_StageObservables_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u
variable {I : Instance} {Seed : Type u}

theorem step_execution_mem (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {s next : State I}
    {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    ∀ e ∈ s.ledger.executions, e ∈ next.ledger.executions := by
  cases hs with
  | write =>
    simp only [record, reportedWriteLedger]
    split_ifs <;> exact fun _ he => he
  | execute => exact fun _ he => List.mem_append_left _ he
  | review | allocate | advance | stop | abandon => exact fun _ he => he

theorem nextFromFrontier_execution_mem (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (s : State I) (action : Action I) (frontier : Frontier input) :
    ∀ e ∈ s.ledger.executions,
      e ∈ (nextFromFrontier input C mode accounting s action frontier).ledger.executions := by
  classical
  unfold nextFromFrontier
  split_ifs with hh hs
  · exact fun _ he => he
  · exact step_execution_mem input C mode accounting _ (Classical.choose_spec hs)
  · exact fun _ he => he

theorem run_execution_mem_after (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    (n extra : ℕ) : ∀ e ∈ (run input C mode accounting rule sample n).ledger.executions,
      e ∈ (run input C mode accounting rule sample (n + extra)).ledger.executions := by
  induction extra with
  | zero => exact fun _ he => he
  | succ extra ih =>
    intro e he
    exact nextFromFrontier_execution_mem input C mode accounting _ _ _ e (ih e he)

theorem historyStageResolved_physical (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) (stage : I.Stage)
    (hresolved : Parameters.historyStageResolved I s.history stage = true) :
    s.ledger.written stage = some (s.ledger.truth stage) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage := by
  classical
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp stage
  cases hb : s.ledger.written stage with
  | none =>
    rw [hb] at hw
    simp [Parameters.historyStageResolved, hw] at hresolved
  | some bit =>
    obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting rule seed truth tapes hp stage (by simp [hb])
    have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp stage
    have hx := prefix_historyExecutions input C mode accounting rule seed truth tapes hp
    rw [hb] at hw
    rw [ht] at hr
    simp only [Parameters.historyStageResolved, hw, hr, Option.map_some, beq_self_eq_true,
      Bool.true_and, Bool.or_eq_true_eq_eq_true_or_eq_true, beq_iff_eq] at hresolved
    rcases hresolved with hbit | hsome
    · exact Or.inl (congrArg some hbit)
    · rw [hx, List.any_map, List.any_eq_true] at hsome
      obtain ⟨e, he, hpair⟩ := hsome
      have hstage : e.handle.stage = stage := by
        have hparts : (e.handle.stage == stage) = true ∧
            (e.handle.writeSerial == s.ledger.writeSerial stage) = true := by
          simpa only [Function.comp_apply, Bool.and_eq_true_eq_eq_true_and_eq_true] using hpair
        exact beq_iff_eq.mp hparts.1
      exact Or.inr ⟨e, he, hstage⟩

theorem survivingEntry_earlier_physically_resolved (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) (stage earlier : P.sharedInstance.Stage)
    (hs : sample ∈ P.survivingEntry fee hf C mode accounting rule stage) (he : earlier.val < stage.val) :
    ∃ n, (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written earlier = some (sample.2 earlier).1 ∨
      ∃ e ∈ (run (P.input fee hf) C.val mode accounting rule sample n).ledger.executions, e.handle.stage = earlier := by
  have hhealthy : ∃ n, Parameters.healthyEntryHistory P.sharedInstance stage
      (run (P.input fee hf) C.val mode accounting rule sample n).history = true := by
    rcases hs with ha | hn
    · cases hh : entryHistory (P.input fee hf) C.val mode accounting rule stage sample with
      | none => simp [Parameters.actualSurvivingEntry, hh, Parameters.healthyEntryRecord] at ha
      | some history =>
        have hhhealthy : Parameters.healthyEntryHistory P.sharedInstance stage history = true := by
          simpa only [Parameters.actualSurvivingEntry, Set.mem_ofPred_eq, hh, Parameters.healthyEntryRecord] using ha
        obtain ⟨n, _, _, hh⟩ := (entryHistory_some_iff (P.input fee hf) C.val mode accounting rule stage sample history).mp hh
        exact ⟨n, hh ▸ hhhealthy⟩
    · obtain ⟨n, _, _, hh⟩ := hn
      exact ⟨n, hh⟩
  obtain ⟨n, hn⟩ := hhealthy
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hf) C.val mode accounting rule hl sample n
  have hphys := historyStageResolved_physical (P.input fee hf) C.val C.property.1.1 mode accounting rule sample.1 _ _ hp earlier
    ((of_decide_eq_true hn) earlier he)
  refine ⟨n, ?_⟩
  simpa only [run_truth (P.input fee hf) C.val mode accounting rule hl, StatisticalInput.truthAt] using hphys

theorem markedError_not_correct_write (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hf) C.val mode accounting rule) (sample : Seed × (P.input fee hf).World)
    (stage : P.sharedInstance.Stage) (hm : sample ∈ P.markedErrorEvent fee hf C mode accounting rule stage) :
    ∀ n, (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written stage ≠ some (sample.2 stage).1 := by
  intro n hw
  have hd := PDROC.actualOrdinaryDecision_of_written P fee hf C mode accounting rule hl sample n stage _ hw
  have hfilled : P.filledOrdinaryDecision fee hf C mode accounting rule sample stage = (sample.2 stage).1 := by
    simp only [Parameters.filledOrdinaryDecision, hd]
  exact hm.2 hfilled

noncomputable def eventualExecutedStages (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World) : Finset I.Stage := by
  classical
  exact Finset.univ.filter (fun stage => ∃ n, ∃ e ∈ (run input C mode accounting rule sample n).ledger.executions,
    e.handle.stage = stage)

theorem eventualExecutedStages_card_le_runRepairCount (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    ((eventualExecutedStages input C mode accounting rule sample).card : ℝ≥0∞) ≤
      runRepairCount input C mode accounting rule sample := by
  classical
  let stages := eventualExecutedStages input C mode accounting rule sample
  have hw (stage : I.Stage) (hm : stage ∈ stages) : ∃ n, ∃ e ∈ (run input C mode accounting rule sample n).ledger.executions,
      e.handle.stage = stage := (Finset.mem_filter.mp hm).2
  let time : I.Stage → ℕ := fun stage => if hm : stage ∈ stages then Nat.find (hw stage hm) else 0
  let bound := stages.sup time
  have hsub : stages ⊆ ((run input C mode accounting rule sample bound).ledger.executions.map (fun e => e.handle.stage)).toFinset := by
    intro stage hm
    have htime : time stage = Nat.find (hw stage hm) := by simp only [time, hm, ↓reduceDIte]
    obtain ⟨e, he, hes⟩ := Nat.find_spec (hw stage hm)
    have hle : Nat.find (hw stage hm) ≤ bound := by simpa only [← htime] using (Finset.le_sup (f := time) hm)
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
    rw [heq]
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e, run_execution_mem_after input C mode accounting rule sample _ extra e he, hes⟩
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  simp only [List.length_map] at hcard
  exact (show (stages.card : ℝ≥0∞) ≤ ((run input C mode accounting rule sample bound).ledger.executions.length : ℝ≥0∞) by exact_mod_cast hcard).trans
    (le_iSup (fun n => ((run input C mode accounting rule sample n).ledger.executions.length : ℝ≥0∞)) bound)

end PDLower
