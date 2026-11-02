module

public import PaperProofs.Retained.PRet_PaymentSelectors_031

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActualPaymentPair032

open Common Common.Native PRetDelayedPolicy010 PRetInformationPackets006 PRetPaymentSelectors031

variable {I : Instance}

theorem canonical_history_handle {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (handle : MismatchHandle I) (hvalid : validHandle s handle) (stage : I.Stage) (hstage : stage = handle.stage) :
    (⟨stage, historyWriteSerial s.history stage⟩ : MismatchHandle I) = handle := by
  have hserial := prefix_historyWriteSerial input C .uncapped accounting rule seed truth tapes hp handle.stage
  have hs : historyWriteSerial s.history handle.stage = handle.writeSerial := hserial.trans hvalid.2.1.symm
  cases handle
  simp_all

/-- The real delayed rule follows the next genuine allocate/execute pair.
Both guards are justified on their actual Prefixes; a terminal cursor N
cannot reject the source stage merely because that stage is earlier. -/
theorem actual_payment_pair {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) (startup : Startup I)
    (hh : startup.halted = true) (hf : startup.finished = true) (hab : startup.abandoned = false)
    (hshadow : shadow accounting source sample.1
      (run input C .uncapped accounting (rule accounting source) sample n).history = some startup)
    (hc : (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount)
    (execution : Execution I) (handle : MismatchHandle I) (tool : I.Tool)
    (hindex : startup.executions[(run input C .uncapped accounting (rule accounting source) sample n).ledger.executions.length]? = some execution)
    (hstage : execution.handle.stage = handle.stage) (htool : execution.tool = tool)
    (committed repaired : State I)
    (ha : Step input C .uncapped accounting (worldTapes input sample.2)
      (run input C .uncapped accounting (rule accounting source) sample n) (.allocate handle tool) committed)
    (he : Step input C .uncapped accounting (worldTapes input sample.2) committed (.execute handle tool) repaired) :
    run input C .uncapped accounting (rule accounting source) sample (n + 2) = repaired ∧
      shadow accounting source sample.1 repaired.history = some startup := by
  let target := run input C .uncapped accounting (rule accounting source) sample n
  have hlegal := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) hlegal sample n
  have hcount : (historyExecutions target.history).length = target.ledger.executions.length := by
    rw [prefix_historyExecutions input C .uncapped accounting (rule accounting source) sample.1 _ _ hp, List.length_map]
  have hvalid : validHandle target handle := by cases ha; assumption
  have hfree : ∀ a ∈ target.ledger.commitments, a.handle.stage ≠ handle.stage := by cases ha; assumption
  have hnone : (historyCommitments target.history).find? (fun pair => pair.1.stage == execution.handle.stage) = none := by
    apply List.find?_eq_none.mpr
    intro pair hpair
    rw [prefix_historyCommitments input C .uncapped accounting (rule accounting source) sample.1 _ _ hp] at hpair
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hpair
    simpa only [hstage, beq_iff_eq] using hfree a ha'
  have hcan := canonical_history_handle input C accounting (rule accounting source) sample.1 _ _ hp handle hvalid _ hstage
  have hcursor : historyCursor target.history = I.stageCount :=
    (prefix_historyCursor input C .uncapped accounting (rule accounting source) sample.1 _ _ hp).trans hc
  have hrawA : raw accounting source sample.1 target.history = .allocate handle tool := by
    rw [raw_payment accounting source sample.1 target.history startup hshadow hh hf hab hcursor,
      payment_allocate startup target.history execution (by rw [hcount]; exact hindex) hnone, hcan, htool]
  have hstepA : Step input C .uncapped accounting (worldTapes input sample.2) target
      (raw accounting source sample.1 target.history) committed := by rw [hrawA]; exact ha
  have hguardA := PRetRetainedGuard007.guarded_action_of_step input C hretained.1 accounting (raw accounting source)
    sample.1 _ _ hp hstepA
  change rule accounting source sample.1 target.history = raw accounting source sample.1 target.history at hguardA
  have hstepA' : Step input C .uncapped accounting (worldTapes input sample.2) target
      (rule accounting source sample.1 target.history) committed := by rw [hguardA]; exact hstepA
  have hnextA := run_succ_of_step input C .uncapped accounting (rule accounting source) sample n committed
    (step_source_active input C .uncapped accounting _ ha) hstepA'
  have hpC := Prefix.next hp hstepA'
  have hshadowC : shadow accounting source sample.1 committed.history = some startup :=
    (step_silent_shadow input C .uncapped accounting source sample.1 _ ha rfl).trans hshadow
  have hcursorC : historyCursor committed.history = I.stageCount := by
    rw [prefix_historyCursor input C .uncapped accounting (rule accounting source) sample.1 _ _ hpC]
    cases ha
    exact hc
  have hindexC : startup.executions[(historyExecutions committed.history).length]? = some execution := by
    rw [prefix_historyExecutions input C .uncapped accounting (rule accounting source) sample.1 _ _ hpC, List.length_map]
    cases ha
    exact hindex
  have hfindC : (historyCommitments committed.history).find? (fun pair => pair.1.stage == execution.handle.stage) = some (handle, tool) := by
    have hhist : historyCommitments committed.history = historyCommitments target.history ++ [(handle, tool)] := by
      cases ha
      simp only [record, historyCommitments, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, eventCommitment]
      rfl
    rw [hhist, List.find?_append, hnone]
    simp only [List.find?_cons, hstage, beq_self_eq_true, Option.none_or]
  have hvalidC : validHandle committed handle := by cases he; assumption
  have hcanC := canonical_history_handle input C accounting (rule accounting source) sample.1 _ _ hpC handle hvalidC _ hstage
  have hrawE : raw accounting source sample.1 committed.history = .execute handle tool := by
    rw [raw_payment accounting source sample.1 committed.history startup hshadowC hh hf hab hcursorC,
      payment_execute startup committed.history execution (handle, tool) hindexC hfindC htool.symm, hcanC, htool]
  have hstepE : Step input C .uncapped accounting (worldTapes input sample.2) committed
      (raw accounting source sample.1 committed.history) repaired := by rw [hrawE]; exact he
  have hguardE := PRetRetainedGuard007.guarded_action_of_step input C hretained.1 accounting (raw accounting source)
    sample.1 _ _ hpC hstepE
  change rule accounting source sample.1 committed.history = raw accounting source sample.1 committed.history at hguardE
  have hstepE' : Step input C .uncapped accounting (worldTapes input sample.2) committed
      (rule accounting source sample.1 committed.history) repaired := by rw [hguardE]; exact hstepE
  have haC := step_source_active input C .uncapped accounting _ he
  have hnextE : run input C .uncapped accounting (rule accounting source) sample (n + 2) = repaired := by
    have hx := run_succ_of_step input C .uncapped accounting (rule accounting source) sample (n + 1) repaired
      (by rw [hnextA]; exact haC) (by rw [hnextA]; exact hstepE')
    exact hx
  exact ⟨hnextE, (step_silent_shadow input C .uncapped accounting source sample.1 _ he rfl).trans hshadowC⟩

end PaperProofs.Retained.PRetActualPaymentPair032
