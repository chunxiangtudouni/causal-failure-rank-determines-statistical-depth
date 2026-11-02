module

public import PaperProofs.Retained.PRet_ActualPaymentList_033
public import PaperProofs.Retained.PRet_SourceSuccess_027
public import PaperProofs.Retained.PRet_EarlyReports_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetTerminalCompletion035

open Common Common.Native PRetExactTerminal001 PRetDelayedPolicy010 PRetInformationPackets006
open PRetActualPaymentList033 PRetPaymentSelectors031 PRetSourceSuccess027 PRetEarlyReports034

variable {I : Instance}

theorem complete_terminal_source {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (oldClock n : ℕ)
    (hhalt : (run input C mode accounting source sample oldClock).halted = true)
    (hsuccess : (run input C mode accounting source sample oldClock).ledger.success C)
    (hcursor : (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount)
    (hactive : (run input C .uncapped accounting (rule accounting source) sample n).halted = false)
    (hshadow : shadow accounting source sample.1
      (run input C .uncapped accounting (rule accounting source) sample n).history =
        some (publicStartup (run input C mode accounting source sample oldClock)))
    (htruth : (run input C .uncapped accounting (rule accounting source) sample n).ledger.truth =
      (run input C mode accounting source sample oldClock).ledger.truth)
    (hwritten : (run input C .uncapped accounting (rule accounting source) sample n).ledger.written =
      (run input C mode accounting source sample oldClock).ledger.written)
    (hcommit : (run input C .uncapped accounting (rule accounting source) sample n).ledger.commitments = [])
    (hexecute : (run input C .uncapped accounting (rule accounting source) sample n).ledger.executions = []) :
    ∃ last, (run input C .uncapped accounting (rule accounting source) sample last).halted = true ∧
      (run input C .uncapped accounting (rule accounting source) sample last).ledger.success C ∧
      (run input C .uncapped accounting (rule accounting source) sample last).ledger.executions.map executionPair =
        (run input C mode accounting source sample oldClock).ledger.executions.map executionPair ∧
      shadow accounting source sample.1
          (run input C .uncapped accounting (rule accounting source) sample last).history =
        some (publicStartup (run input C mode accounting source sample oldClock)) := by
  let original := run input C mode accounting source sample oldClock
  let target := run input C .uncapped accounting (rule accounting source) sample n
  let startup := publicStartup original
  change target.ledger.truth = original.ledger.truth at htruth
  change target.ledger.written = original.ledger.written at hwritten
  change target.ledger.commitments = [] at hcommit
  change target.ledger.executions = [] at hexecute
  change original.ledger.success C at hsuccess
  have htargetLegal := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htargetLegal sample n
  have hinvariant := prefix_invariant input C .uncapped accounting (rule accounting source) sample.1 _ _ hp
  have hsourceWF := run_ledgerWellFormed input C mode accounting source hlegal sample oldClock
  change LedgerWellFormed original.ledger at hsourceWF
  have hhandles : ∀ e ∈ original.ledger.executions, validHandle target (originalHandle target e.handle.stage) := by
    intro e he
    have hg := (hsourceWF.genuine e he).1
    refine ⟨?_, rfl, ?_⟩
    · simpa only [originalHandle, hwritten, htruth] using hg
    · apply (prefix_written_reported input C hretained.1 .uncapped accounting (rule accounting source) sample.1 _ _ hp e.handle.stage)
      change target.ledger.written e.handle.stage ≠ none
      rw [hwritten, hg]
      exact Option.some_ne_none _
  obtain ⟨last, _, final, hrunFinal, haFinal, hcFinal, htFinal, hwFinal, hsFinal, hpaidFinal⟩ :=
    follow_paid_tail input C hretained accounting source sample startup hhalt hsuccess.1 hsuccess.2.1
      target original.ledger.executions hsourceWF.execution_stages hsourceWF.execution_tools hsourceWF.compatible
      [] rfl n target rfl hinvariant hactive hcursor hshadow (by simp only [hexecute, List.map_nil])
      hhandles (by simp only [hcommit, List.not_mem_nil, forall_false, implies_true])
      (by simp only [hcommit, List.not_mem_nil, forall_false, implies_true])
  obtain ⟨_, _, hpFinal⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htargetLegal sample last
  rw [hrunFinal] at hpFinal
  have hcursorFinal : historyCursor final.history = I.stageCount :=
    (prefix_historyCursor input C .uncapped accounting (rule accounting source) sample.1 _ _ hpFinal).trans (hcFinal.trans hcursor)
  have hlength : final.ledger.executions.length = startup.executions.length := by
    have hl := congrArg List.length hpaidFinal
    simpa only [List.length_map] using hl
  have hnone : startup.executions[(historyExecutions final.history).length]? = none := by
    rw [prefix_historyExecutions input C .uncapped accounting (rule accounting source) sample.1 _ _ hpFinal,
      List.length_map, hlength]
    exact List.getElem?_eq_none le_rfl
  have hraw : raw accounting source sample.1 final.history = .stop := by
    rw [raw_payment accounting source sample.1 final.history startup hsFinal hhalt hsuccess.1 hsuccess.2.1 hcursorFinal,
      paymentAction, hnone]
  have hstop : Step input C .uncapped accounting (worldTapes input sample.2) final
      (raw accounting source sample.1 final.history) (stopState final false) := by
    rw [hraw]
    exact Step.stop final haFinal
  have hguard := PRetRetainedGuard007.guarded_action_of_step input C hretained.1 accounting (raw accounting source)
    sample.1 _ _ hpFinal hstop
  change rule accounting source sample.1 final.history = raw accounting source sample.1 final.history at hguard
  have hrunStop := run_succ_of_step input C .uncapped accounting (rule accounting source) sample last (stopState final false)
    (by rw [hrunFinal]; exact haFinal) (by rw [hrunFinal, hguard]; exact hstop)
  refine ⟨last + 1, ?_, ?_, ?_, ?_⟩
  · rw [hrunStop]
    rfl
  · rw [hrunStop]
    refine ⟨?_, rfl, ?_, ?_⟩
    · have hall : allWritten final.ledger := by
        intro stage
        rw [hwFinal, hwritten]
        exact success_allWritten C original.ledger hsourceWF hsuccess stage
      simp only [stopState, hall, decide_true]
    · simp [Ledger.windowObligations, hretained.2.1, hretained.2.2]
    · intro stage
      obtain hcorrect | ⟨e, he, hstage⟩ := hsuccess.2.2.2 stage
      · exact Or.inl (by simpa only [stopState, hwFinal, htFinal, hwritten, htruth] using hcorrect)
      · right
        have hm : executionPair e ∈ final.ledger.executions.map executionPair := by
          rw [hpaidFinal]
          exact List.mem_map.mpr ⟨e, he, rfl⟩
        obtain ⟨e', he', heq⟩ := List.mem_map.mp hm
        exact ⟨e', he', (congrArg Prod.fst heq).trans hstage⟩
  · rw [hrunStop]
    exact hpaidFinal
  · rw [hrunStop]
    exact (step_silent_shadow input C .uncapped accounting source sample.1 (worldTapes input sample.2)
      (Step.stop final haFinal) rfl).trans hsFinal

end PaperProofs.Retained.PRetTerminalCompletion035
