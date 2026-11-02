module

public import PaperProofs.Paid.PDMenu_CurrentReplayRun_023
public import PaperProofs.Common.HistorySuffixSuccess

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

variable {I : Instance} {Seed : Type*}

noncomputable def paidReplayedSuffixAvailablePolicy [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (startup : Startup I) :
    AvailablePolicy (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) startup.availableTools Seed := by
  let raw := replayedSuffixCandidate first accounting rule startup
  exact ⟨{
    rule := paidGuardedRule startup.availableTools raw
    measurable_rule := measurable_paidGuardedRule _ _ (measurable_replayedSuffixCandidate first accounting rule hm startup)
    legal := paidGuardedRule_legal _ _ rfl _ _ raw },
    paidGuardedRule_usesOnly _ _ _ _ raw⟩

theorem paidReplayedSuffix_prefix_observationBill (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample) (k : ℕ) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) k).ledger.observationBill
        (input.freshSuffix first).fees =
      observationIncrement input (run input C mode accounting rule sample start)
        (run input C mode accounting rule sample (replaySourceClock input C mode accounting rule sample first start k)) := by
  have hv := (paidReplayedSuffix_fullRun input C hearly hcurrent hpayment mode accounting rule hlegal sample first start hentry k).1
  rw [firstEntry_observationIncrement_eq_future_sum input C mode accounting rule hlegal sample first start _ hentry
    (replaySourceClock_ge_start input C mode accounting rule sample first start k)]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro stage _
  have hf : first ≤ (I.freshStageLift first stage).val := by change first ≤ first + stage.val; omega
  have hh := hv.reviews (I.freshStageLift first stage) hf
  rw [suffixStageOf_freshStageLift] at hh
  have hfee : (input.freshSuffix first).fees.observation stage = input.fees.observation (I.freshStageLift first stage) :=
    congrArg BinaryExperiment.observationFee (input.freshSuffix_experiment first stage)
  rw [hfee, hh]

theorem paidReplayedSuffix_observationBill_eq (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    runObservationBill (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) =
      futureObservationBill input C mode accounting rule start sample := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetAt := fun k => run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) k
  let clock := replaySourceClock input C mode accounting rule sample first start
  let g := fun n => observationIncrement input (run input C mode accounting rule sample start)
    (run input C mode accounting rule sample n)
  have hmono : Monotone g := by
    intro a b hab
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono
      (tsub_le_tsub_right (run_reviews_mono input C mode accounting rule hlegal sample stage hab) _)) _
  have hprefix (k : ℕ) : (targetAt k).ledger.observationBill (input.freshSuffix first).fees = g (clock k) :=
    paidReplayedSuffix_prefix_observationBill input C hearly hcurrent hpayment mode accounting rule hlegal sample first start hentry k
  change (⨆ k, (targetAt k).ledger.observationBill (input.freshSuffix first).fees) = ⨆ extra, g (start + extra)
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [hprefix]
    obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (replaySourceClock_ge_start input C mode accounting rule sample first start k)
    change clock k = start + extra at he
    rw [he]
    exact le_iSup (fun extra => g (start + extra)) extra
  · apply iSup_le
    intro extra
    have hcofinal : g (start + extra) ≤ g (clock extra) := by
      rcases replaySourceClock_grows_or_halted input C mode accounting rule sample first start extra with hbound | hhalt
      · exact hmono hbound
      · by_cases hle : start + extra ≤ clock extra
        · exact hmono hle
        · obtain ⟨delta, he⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hle)
          change start + extra = clock extra + delta at he
          change observationIncrement input _ _ ≤ observationIncrement input _ _
          rw [he, run_after_halt input C mode accounting rule sample (clock extra) hhalt delta]
    exact hcofinal.trans ((hprefix extra).symm.le.trans (le_iSup (fun k => (targetAt k).ledger.observationBill (input.freshSuffix first).fees) extra))

theorem paidReplayedSuffix_runSuccess (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample)
    (hsuccess : runSuccess input C mode accounting rule sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    runSuccess (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let sourceAt := fun n => run input C mode accounting rule sample n
  let targetAt := fun k => run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  have htargetLegal : LegalRule (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule := paidGuardedRule_legal _ _ rfl _ _ _
  obtain ⟨stopped, hsHalt, hsSuccess⟩ := hsuccess
  obtain ⟨k, hsame⟩ := replaySourceClock_reaches_halted input C mode accounting rule sample first start stopped hsHalt
  let clock := replaySourceClock input C mode accounting rule sample first start k
  change sourceAt clock = sourceAt stopped at hsame
  have hsourceHalt : (sourceAt clock).halted = true := by rw [hsame]; exact hsHalt
  have hsourceSuccess : (sourceAt clock).ledger.success C := by rw [hsame]; exact hsSuccess
  obtain ⟨view, hreplay⟩ := paidReplayedSuffix_fullRun input C hearly hcurrent hpayment mode accounting rule hlegal sample first start hentry k
  have htargetHalt : (targetAt k).halted = true := view.halted.symm.trans hsourceHalt
  obtain ⟨targetN, _, targetPrefix⟩ := run_has_prefix (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule htargetLegal targetSample k
  obtain ⟨entryN, _, entryPrefix⟩ := run_has_prefix input C mode accounting rule hlegal sample start
  have entryInv := prefix_invariant input C mode accounting rule sample.1 _ _ entryPrefix
  have entryFacts := firstEntryAt_unborn input C mode accounting rule hlegal sample first start hentry
  have hentryExec : ∀ e ∈ startup.executions, e.handle.stage.val < first := by
    intro e he
    by_contra hf
    have hfuture := Nat.le_of_not_gt hf
    have hg := (entryInv.wellFormed.genuine e he).1
    rw [(entryFacts.2 e.handle.stage hfuture).1] at hg
    cases hg
  obtain ⟨packets, _, hpackets⟩ := prefix_parseSuffixPackets (input.freshSuffix first)
    (paidRelaxedContract (I.freshSuffix first)) rfl .uncapped (zeroNormalAccounting (I.freshSuffix first))
    targetRule sample.1 _ _ targetPrefix
  have hcover := replaySuffixHistory_future_execution first accounting rule sample.1 startup (publicStartup (sourceAt clock))
    (targetAt k).history packets hpackets hreplay hentryExec
  have hlast := replaySuffixHistory_halted_stopped first accounting rule sample.1 startup (publicStartup (sourceAt clock))
    (targetAt k).history packets hpackets hreplay entryFacts.1 hsourceHalt hsourceSuccess.2.1
  have htargetAbandoned := prefix_last_stopped_not_abandoned (input.freshSuffix first)
    (paidRelaxedContract (I.freshSuffix first)) rfl .uncapped (zeroNormalAccounting (I.freshSuffix first))
    targetRule sample.1 _ _ targetPrefix hlast
  have hcorrect (stage : (I.freshSuffix first).Stage) :
      (targetAt k).ledger.written stage = some ((targetAt k).ledger.truth stage) ∨
        ∃ e ∈ (targetAt k).ledger.executions, e.handle.stage = stage := by
    have hf : first ≤ (I.freshStageLift first stage).val := by change first ≤ first + stage.val; omega
    rcases hsourceSuccess.2.2.2 (I.freshStageLift first stage) with hright | ⟨e, he, hes⟩
    · have hw := view.written (I.freshStageLift first stage) hf
      have ht := view.truth (I.freshStageLift first stage) hf
      rw [suffixStageOf_freshStageLift] at hw ht
      rw [← hw, ← ht] at hright
      exact .inl hright
    · have hfe : first ≤ e.handle.stage.val := by rw [hes]; exact hf
      obtain ⟨pair, hp, hstage, _⟩ := hcover e he hfe
      have hlower : suffixStageOf first e.handle.stage hfe = stage := by
        apply Fin.ext
        change e.handle.stage.val - first = stage.val
        have hh := congrArg Fin.val hes
        change e.handle.stage.val = first + stage.val at hh
        omega
      rw [hlower] at hstage
      rw [prefix_historyExecutions (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ targetPrefix] at hp
      obtain ⟨targetE, htargetE, heq⟩ := List.mem_map.mp hp
      exact .inr ⟨targetE, htargetE, (congrArg (fun p => p.1.stage) heq).trans hstage⟩
  have targetInv := prefix_ledgerWellFormed (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ targetPrefix
  have hallWritten : allWritten (targetAt k).ledger := by
    intro stage
    rcases hcorrect stage with hright | ⟨e, he, hes⟩
    · rw [hright]
      intro hn
      cases hn
    · have hg := (targetInv.genuine e he).1
      rw [hes] at hg
      rw [hg]
      intro hn
      cases hn
  have hfinished := prefix_halted_allWritten_finished (input.freshSuffix first)
    (paidRelaxedContract (I.freshSuffix first)) .uncapped (zeroNormalAccounting (I.freshSuffix first))
    targetRule sample.1 _ _ targetPrefix htargetHalt hallWritten
  refine ⟨k, htargetHalt, ?_⟩
  apply (prefix_success_iff_physical (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ targetPrefix).mpr
  exact ⟨hfinished, htargetAbandoned, fun stage => (finalOutput_correct_iff _ stage).mpr (hcorrect stage)⟩


end PDMenu
