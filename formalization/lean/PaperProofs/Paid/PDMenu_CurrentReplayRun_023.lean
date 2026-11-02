module

public import PaperProofs.Paid.PDMenu_CurrentReplayStep_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

theorem paidReplayedSuffix_fullRun (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools (replayedSuffixCandidate first accounting rule startup)
    let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
    ∀ k : ℕ,
      HistorySuffixStateView input first
        (run input C mode accounting rule sample (replaySourceClock input C mode accounting rule sample first start k))
        (run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k) ∧
      replaySuffixHistory first accounting rule sample.1 startup
        (run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k).history =
        some (publicStartup (run input C mode accounting rule sample
          (replaySourceClock input C mode accounting rule sample first start k))) := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let raw := replayedSuffixCandidate first accounting rule startup
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools raw
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let sourceAt := fun n => run input C mode accounting rule sample n
  let targetAt := fun k => run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  have htargetLegal : LegalRule (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule := paidGuardedRule_legal _ _ rfl _ _ raw
  change ∀ k, HistorySuffixStateView input first (sourceAt (replaySourceClock input C mode accounting rule sample first start k)) (targetAt k) ∧
    replaySuffixHistory first accounting rule sample.1 startup (targetAt k).history =
      some (publicStartup (sourceAt (replaySourceClock input C mode accounting rule sample first start k)))
  intro k
  induction k with
  | zero =>
    exact ⟨historySuffixStateView_firstEntry input C mode accounting rule hlegal sample first start hentry, rfl⟩
  | succ k ih =>
    let n := replaySourceClock input C mode accounting rule sample first start k
    let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 (publicStartup (sourceAt n))
    change HistorySuffixStateView input first (sourceAt n) (targetAt k) ∧
      replaySuffixHistory first accounting rule sample.1 startup (targetAt k).history = some (publicStartup (sourceAt n)) at ih
    have hclock : replaySourceClock input C mode accounting rule sample first start (k + 1) =
        if (sourceAt n).halted then n else n + result.2 + 1 := rfl
    rw [hclock]
    cases hh : (sourceAt n).halted with
    | true =>
      have ht : (targetAt k).halted = true := ih.1.halted.symm.trans hh
      have hr := run_succ_of_halted (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k ht
      change targetAt (k + 1) = targetAt k at hr
      simp only [↓reduceIte, hr]
      exact ih
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have htargetActive : (targetAt k).halted = false := ih.1.halted.symm.trans hh
      have hr : result.1 = publicStartup (sourceAt (n + result.2)) :=
        settleOldExecutions_actual input C mode accounting rule hlegal sample first _ n
      have hresultActive : result.1.halted = false :=
        (settleOldExecutions_halted first accounting rule (I.toolCount + 1) sample.1 (publicStartup (sourceAt n))).trans hh
      have hsettledActive : (sourceAt (n + result.2)).halted = false := by rw [hr] at hresultActive; exact hresultActive
      have hcursor : first ≤ (sourceAt n).cursor := by have hc := ih.1.cursor; omega
      have hview : HistorySuffixStateView input first (sourceAt (n + result.2)) (targetAt k) :=
        ih.1.settleOld input first C mode accounting rule hlegal sample (I.toolCount + 1) n (targetAt k)
      obtain ⟨sourceNext, hs, hproject⟩ := suffixActionAtPublicCache_actual input C mode accounting rule hlegal hcurrent
        sample first n (targetAt k).history hcursor hresultActive
      have hraw : raw sample.1 (targetAt k).history = suffixActionAtPublicCache first accounting rule sample.1
          (publicStartup (sourceAt n)) (targetAt k).history := by
        change (match replaySuffixHistory first accounting rule sample.1 startup (targetAt k).history with
          | none => (Action.abandon : Action (I.freshSuffix first)) | some cache => suffixActionAtPublicCache first accounting rule sample.1 cache (targetAt k).history) = _
        rw [ih.2]
      have hprojectRaw : suffixActionOf first (targetAt k).history (rule sample.1 result.1.history) =
          some (raw sample.1 (targetAt k).history) := by rw [hraw]; exact hproject
      change Step input C mode accounting (worldTapes input sample.2) (sourceAt (n + result.2))
        (rule sample.1 result.1.history) sourceNext at hs
      rw [hr] at hs hprojectRaw
      obtain ⟨targetPrefixN, _, targetPrefix⟩ := run_has_prefix (input.freshSuffix first)
        (paidRelaxedContract (I.freshSuffix first)) .uncapped (zeroNormalAccounting (I.freshSuffix first))
        targetRule htargetLegal targetSample k
      obtain ⟨targetNext, ht⟩ := paidHistorySuffixStep input first C hcurrent hpayment mode accounting (worldTapes input sample.2)
        (worldTapes (input.freshSuffix first) targetSample.2) targetRule sample.1 _ targetPrefix hview hprojectRaw hs
      have havailable : ∀ handle tool, raw sample.1 (targetAt k).history = .allocate handle tool → tool ∈ startup.availableTools := by
        intro handle tool ha
        have hp := hprojectRaw
        rw [ha] at hp
        obtain ⟨sourceHandle, hsourceAction⟩ := suffixActionOf_allocate_source first (targetAt k).history _ handle tool hp
        have halloc : Step input C mode accounting (worldTapes input sample.2) (sourceAt (n + result.2))
            (.allocate sourceHandle tool) sourceNext := by rw [← hsourceAction]; exact hs
        exact allocated_tool_available_at_saved_prefix input C mode accounting rule hlegal sample start (n + result.2)
          (by have hn := replaySourceClock_ge_start input C mode accounting rule sample first start k; change start ≤ n at hn; omega)
          sourceHandle tool halloc
      have hguard := paidGuardedRule_eq_of_step (input.freshSuffix first)
        (paidRelaxedContract (I.freshSuffix first)) (paidRelaxedContract_rights _) (zeroNormalAccounting (I.freshSuffix first))
        targetRule raw sample.1 _ _ targetPrefix startup.availableTools ht havailable
      have htargetPolicy : targetRule sample.1 (targetAt k).history = raw sample.1 (targetAt k).history := hguard
      have htargetStep : Step (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) (worldTapes (input.freshSuffix first) targetSample.2)
          (targetAt k) (targetRule sample.1 (targetAt k).history) targetNext := by rw [htargetPolicy]; exact ht
      have htargetRun := run_succ_of_step (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k targetNext htargetActive htargetStep
      have hsourceRun := run_succ_of_step input C mode accounting rule sample (n + result.2) sourceNext hsettledActive hs
      obtain ⟨sourcePrefixN, _, sourcePrefix⟩ := run_has_prefix input C mode accounting rule hlegal sample (n + result.2)
      have hnextView := hview.next input first C hearly mode accounting _ _
        (prefix_invariant input C mode accounting rule sample.1 _ _ sourcePrefix) hprojectRaw hs
        (step_to_deferred _ _ .uncapped _ _ ht)
      obtain ⟨packet, hhistory, hreplay⟩ := replaySuffixPacket_real_target input C hearly mode accounting first rule sample.1
        sample.2 (publicStartup (sourceAt n)) (sourceAt (n + result.2)) sourceNext (targetAt k) targetNext
        (raw sample.1 (targetAt k).history) hr hsettledActive hs
        (step_to_deferred _ _ .uncapped _ _ ht) hprojectRaw
        (run_truth input C mode accounting rule hlegal sample (n + result.2))
        (run_truth (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) targetRule htargetLegal targetSample k) hview.reviews
      obtain ⟨packets, _, hpackets⟩ := prefix_parseSuffixPackets (input.freshSuffix first)
        (paidRelaxedContract (I.freshSuffix first)) rfl .uncapped (zeroNormalAccounting (I.freshSuffix first))
        targetRule sample.1 _ _ targetPrefix
      have hnextReplay : replaySuffixHistory first accounting rule sample.1 startup targetNext.history = some (publicStartup sourceNext) := by
        rw [hhistory, ← hpackets, replaySuffixHistory_append_packet]
        rw [hpackets, ih.2, Option.bind_some]
        exact hreplay
      change targetAt (k + 1) = targetNext at htargetRun
      change sourceAt (n + result.2 + 1) = sourceNext at hsourceRun
      rw [htargetRun, hsourceRun]
      exact ⟨hnextView, hnextReplay⟩


end PDMenu
