module

public import PaperProofs.Common.HistorySuffixCharge
import Lean.Elab.Tactic.Omega

/-! Future executions in the actual B09 response replay. No execution
correspondence or success domination is assumed as a controller premise. -/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem settleOldExecutions_future_execution (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (fuel : ℕ) (seed : Seed) (startup : Startup I)
    (e : Execution I)
    (he : e ∈ (settleOldExecutions first accounting rule fuel seed startup).1.executions)
    (hf : first ≤ e.handle.stage.val) : e ∈ startup.executions := by
  induction fuel generalizing startup with
  | zero => exact he
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting startup (rule seed startup.history) = next
    cases next with
    | none => simpa only [settleOldExecutions, hn] using he
    | some next =>
      obtain ⟨_, handle, tool, _, hold, rfl⟩ :=
        (silentOldNext_some_iff first accounting startup next _).mp hn
      simp only [settleOldExecutions, hn] at he
      have hem := ih _ he
      change e ∈ startup.executions ++ [⟨handle, tool, startup.clock⟩] at hem
      rcases List.mem_append.mp hem with h | h
      · exact h
      · have heq := List.mem_singleton.mp h
        subst e
        exact (Nat.not_le_of_gt hold hf).elim

def FutureExecutionCover (first : ℕ) (history : List (VisibleEvent (I.freshSuffix first)))
    (cache : Startup I) : Prop :=
  ∀ e ∈ cache.executions, ∀ hf : first ≤ e.handle.stage.val,
    ∃ pair ∈ historyExecutions history,
      pair.1.stage = suffixStageOf first e.handle.stage hf ∧ pair.2 = e.tool

theorem FutureExecutionCover.settleOld (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (fuel : ℕ) (seed : Seed) (startup : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) (cover : FutureExecutionCover first history startup) :
    FutureExecutionCover first history (settleOldExecutions first accounting rule fuel seed startup).1 := by
  intro e he hf
  exact cover e (settleOldExecutions_future_execution first accounting rule fuel seed startup e he hf) hf

theorem FutureExecutionCover.append (first : ℕ)
    (history extra : List (VisibleEvent (I.freshSuffix first))) (startup : Startup I)
    (cover : FutureExecutionCover first history startup) :
    FutureExecutionCover first (history ++ extra) startup := by
  intro e he hf
  obtain ⟨pair, hp, hs, ht⟩ := cover e he hf
  exact ⟨pair, by simpa only [historyExecutions, List.filterMap_append] using List.mem_append_left (extra.filterMap eventExecution) hp, hs, ht⟩

theorem applySuffixPacketPublic_future_execution (first : ℕ) (accounting : NormalAccounting I)
    (cache next : Startup I) (history : List (VisibleEvent (I.freshSuffix first)))
    (action : Action I) (packet : SuffixPacket (I.freshSuffix first))
    (hproject : suffixActionOf first history action = some packet.action)
    (hupdate : applySuffixPacketPublic accounting cache action packet = some next)
    (cover : FutureExecutionCover first history cache) :
    FutureExecutionCover first (history ++ packet.events) next := by
  cases action <;> cases packet <;> simp only [applySuffixPacketPublic, reduceCtorEq] at hupdate
  all_goals cases hupdate
  all_goals try exact cover.append first history _ cache
  rename_i sourceHandle sourceTool targetHandle targetTool
  simp only [suffixActionOf, SuffixPacket.action] at hproject
  split at hproject
  next hf =>
    have hp := Option.some.inj hproject
    obtain ⟨hh, ht⟩ := Action.execute.inj hp
    subst targetHandle
    subst targetTool
    intro e he hfuture
    change e ∈ cache.executions ++ [⟨sourceHandle, sourceTool, cache.clock⟩] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact (cover.append first history _ cache) e hold hfuture
    · obtain rfl := List.mem_singleton.mp hnew
      refine ⟨(suffixHandleOf first history sourceHandle hf, sourceTool), ?_, rfl, rfl⟩
      simp only [historyExecutions, List.filterMap_append, SuffixPacket.events, List.filterMap_cons,
        List.filterMap_nil, eventExecution, List.mem_append, List.mem_singleton, or_true]
  next hf => cases hproject

theorem replaySuffixPacket_future_execution (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket (I.freshSuffix first))
    (hreplay : replaySuffixPacket first accounting rule seed cache history packet = some next)
    (cover : FutureExecutionCover first history cache) :
    FutureExecutionCover first (history ++ packet.events) next := by
  let settled := (settleOldExecutions first accounting rule (I.toolCount + 1) seed cache).1
  change (if settled.halted then none else
    if suffixActionOf first history (rule seed settled.history) = some packet.action then
      applySuffixPacketPublic accounting settled (rule seed settled.history) packet else none) = some next at hreplay
  split at hreplay
  next hhalt => cases hreplay
  next hhalt =>
    split at hreplay
    next hproject =>
      exact applySuffixPacketPublic_future_execution first accounting settled next history _ packet hproject hreplay
        (cover.settleOld first accounting rule (I.toolCount + 1) seed cache history)
    next hproject => cases hreplay

theorem replaySuffixPackets_future_execution (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (packets : List (SuffixPacket (I.freshSuffix first)))
    (hreplay : replaySuffixPackets first accounting rule seed cache history packets = some next)
    (cover : FutureExecutionCover first history cache) :
    FutureExecutionCover first (history ++ packets.flatMap SuffixPacket.events) next := by
  induction packets generalizing cache history with
  | nil =>
    simp only [replaySuffixPackets, Option.some.injEq] at hreplay
    subst next
    simpa only [List.flatMap_nil, List.append_nil] using cover
  | cons packet rest ih =>
    simp only [replaySuffixPackets, Option.bind_eq_some_iff] at hreplay
    obtain ⟨mid, hfirst, hrest⟩ := hreplay
    have hc := replaySuffixPacket_future_execution first accounting rule seed cache mid history packet hfirst cover
    simpa only [List.flatMap_cons, List.append_assoc] using ih mid (history ++ packet.events) hrest hc

theorem replaySuffixHistory_future_execution (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (packets : List (SuffixPacket (I.freshSuffix first)))
    (hhistory : packets.flatMap SuffixPacket.events = history)
    (hreplay : replaySuffixHistory first accounting rule seed cache history = some next)
    (hcache : ∀ e ∈ cache.executions, e.handle.stage.val < first) :
    FutureExecutionCover first history next := by
  have hc : FutureExecutionCover first [] cache := by
    intro e he hf
    exact (Nat.not_le_of_gt (hcache e he) hf).elim
  rw [← hhistory, replaySuffixHistory_packets] at hreplay
  have hh := replaySuffixPackets_future_execution first accounting rule seed cache next [] packets hreplay hc
  simpa only [List.nil_append, hhistory] using hh

theorem replaySuffixPacket_active (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket (I.freshSuffix first))
    (hreplay : replaySuffixPacket first accounting rule seed cache history packet = some next) :
    cache.halted = false := by
  by_contra hh
  have ht : cache.halted = true := by
    cases hc : cache.halted
    · exact (hh hc).elim
    · rfl
  have hs := settleOldExecutions_halted first accounting rule (I.toolCount + 1) seed cache
  dsimp only [replaySuffixPacket] at hreplay
  rw [hs, ht] at hreplay
  cases hreplay

theorem replaySuffixPacket_halted_stopped (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) (packet : SuffixPacket (I.freshSuffix first))
    (hreplay : replaySuffixPacket first accounting rule seed cache history packet = some next)
    (hhalt : next.halted = true) (habandon : next.abandoned = false) : packet = .stop := by
  let settled := (settleOldExecutions first accounting rule (I.toolCount + 1) seed cache).1
  change (if settled.halted then none else
    if suffixActionOf first history (rule seed settled.history) = some packet.action then
      applySuffixPacketPublic accounting settled (rule seed settled.history) packet else none) = some next at hreplay
  split at hreplay
  next hh => cases hreplay
  next hh =>
    split at hreplay
    next hproject =>
      generalize rule seed settled.history = action at hreplay
      cases action <;> cases packet <;> simp only [applySuffixPacketPublic, reduceCtorEq] at hreplay
      all_goals cases hreplay
      all_goals solve | exact rfl | cases hhalt | (change true = false at habandon; cases habandon)
    next hproject => cases hreplay

theorem replaySuffixPackets_halted_stopped (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (packets : List (SuffixPacket (I.freshSuffix first)))
    (hreplay : replaySuffixPackets first accounting rule seed cache history packets = some next)
    (hactive : cache.halted = false) (hhalt : next.halted = true) (habandon : next.abandoned = false) :
    (packets.flatMap SuffixPacket.events).getLast? = some .stopped := by
  induction packets generalizing cache history with
  | nil =>
    simp only [replaySuffixPackets, Option.some.injEq] at hreplay
    subst next
    rw [hactive] at hhalt
    cases hhalt
  | cons packet rest ih =>
    simp only [replaySuffixPackets, Option.bind_eq_some_iff] at hreplay
    obtain ⟨mid, hfirst, hrest⟩ := hreplay
    cases rest with
    | nil =>
      simp only [replaySuffixPackets, Option.some.injEq] at hrest
      subst next
      have hp := replaySuffixPacket_halted_stopped first accounting rule seed cache mid history packet hfirst hhalt habandon
      subst packet
      rfl
    | cons nextPacket more =>
      have hm : mid.halted = false := by
        have hr := hrest
        simp only [replaySuffixPackets, Option.bind_eq_some_iff] at hr
        obtain ⟨after, ha, _⟩ := hr
        exact replaySuffixPacket_active first accounting rule seed mid after (history ++ packet.events) nextPacket ha
      have hl := ih mid (history ++ packet.events) hrest hm
      simp only [List.flatMap_cons] at hl
      simp only [List.flatMap_cons]
      rw [List.getLast?_append]
      rw [hl]
      rfl

theorem replaySuffixHistory_halted_stopped (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (cache next : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (packets : List (SuffixPacket (I.freshSuffix first)))
    (hhistory : packets.flatMap SuffixPacket.events = history)
    (hreplay : replaySuffixHistory first accounting rule seed cache history = some next)
    (hactive : cache.halted = false) (hhalt : next.halted = true) (habandon : next.abandoned = false) :
    history.getLast? = some .stopped := by
  rw [← hhistory, replaySuffixHistory_packets] at hreplay
  rw [← hhistory]
  exact replaySuffixPackets_halted_stopped first accounting rule seed cache next [] packets hreplay hactive hhalt habandon

theorem prefix_halted_allWritten_finished (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hhalt : s.halted = true) (hwritten : allWritten s.ledger) : s.ledger.finished = true := by
  classical
  cases hp with
  | initial => cases hhalt
  | next earlier hs =>
    generalize rule seed _ = action at hs
    cases hs <;> try cases hhalt
    all_goals
      apply decide_eq_true
      exact hwritten

theorem prefix_last_stopped_not_abandoned (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hlast : s.history.getLast? = some .stopped) : s.ledger.abandoned = false := by
  cases hp with
  | initial => cases hlast
  | next earlier hs =>
    generalize rule seed _ = action at hs
    cases hs <;> try rfl
    all_goals simp only [record, stopState, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.getLast?_append, List.getLast?_cons, List.getLast?_nil,
      Option.some_or] at hlast
    all_goals cases hlast

theorem replaySourceClock_reaches_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (first start stopped : ℕ)
    (hstop : (run input C mode accounting rule sample stopped).halted = true) :
    ∃ k, run input C mode accounting rule sample (replaySourceClock input C mode accounting rule sample first start k) =
      run input C mode accounting rule sample stopped := by
  refine ⟨stopped, ?_⟩
  let clock := replaySourceClock input C mode accounting rule sample first start stopped
  change run input C mode accounting rule sample clock = _
  rcases replaySourceClock_grows_or_halted input C mode accounting rule sample first start stopped with hbound | hhalt
  · have hle : stopped ≤ clock := by omega
    obtain ⟨delta, he⟩ := Nat.exists_eq_add_of_le hle
    rw [he, run_after_halt input C mode accounting rule sample stopped hstop delta]
  · rcases le_total stopped clock with hle | hle
    · obtain ⟨delta, he⟩ := Nat.exists_eq_add_of_le hle
      rw [he, run_after_halt input C mode accounting rule sample stopped hstop delta]
    · obtain ⟨delta, he⟩ := Nat.exists_eq_add_of_le hle
      rw [he, run_after_halt input C mode accounting rule sample clock hhalt delta]

/-- Eventual success of the original strategy implies eventual success of
the concrete fresh-suffix replay. All future actual source executions are
extracted from genuine response replay, not assumed as an extra view field.
Old unexecuted obligations can make the source fail without making the suffix
fail; only the required domination direction is claimed. -/
theorem replayedSuffix_runSuccess (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample)
    (hsuccess : runSuccess input C mode accounting rule sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    runSuccess (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let sourceAt := fun n => run input C mode accounting rule sample n
  let targetAt := fun k => run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  have htargetLegal : LegalRule (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule := guardedReplayRule_legal _ _ rfl rfl _ _ _
  obtain ⟨stopped, hsHalt, hsSuccess⟩ := hsuccess
  obtain ⟨k, hsame⟩ := replaySourceClock_reaches_halted input C mode accounting rule sample first start stopped hsHalt
  let clock := replaySourceClock input C mode accounting rule sample first start k
  change sourceAt clock = sourceAt stopped at hsame
  have hsourceHalt : (sourceAt clock).halted = true := by rw [hsame]; exact hsHalt
  have hsourceSuccess : (sourceAt clock).ledger.success C := by rw [hsame]; exact hsSuccess
  obtain ⟨view, hreplay⟩ := replayedSuffix_fullRun input C hearly hcurrent mode accounting rule hlegal sample first start hentry k
  have htargetHalt : (targetAt k).halted = true := view.halted.symm.trans hsourceHalt
  obtain ⟨targetN, _, targetPrefix⟩ := run_has_prefix (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
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
    (currentRelaxedContract (I.freshSuffix first)) rfl .uncapped (zeroNormalAccounting (I.freshSuffix first))
    targetRule sample.1 _ _ targetPrefix
  have hcover := replaySuffixHistory_future_execution first accounting rule sample.1 startup (publicStartup (sourceAt clock))
    (targetAt k).history packets hpackets hreplay hentryExec
  have hlast := replaySuffixHistory_halted_stopped first accounting rule sample.1 startup (publicStartup (sourceAt clock))
    (targetAt k).history packets hpackets hreplay entryFacts.1 hsourceHalt hsourceSuccess.2.1
  have htargetAbandoned := prefix_last_stopped_not_abandoned (input.freshSuffix first)
    (currentRelaxedContract (I.freshSuffix first)) rfl .uncapped (zeroNormalAccounting (I.freshSuffix first))
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
      rw [prefix_historyExecutions (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
        .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ targetPrefix] at hp
      obtain ⟨targetE, htargetE, heq⟩ := List.mem_map.mp hp
      exact .inr ⟨targetE, htargetE, (congrArg (fun p => p.1.stage) heq).trans hstage⟩
  have targetInv := prefix_ledgerWellFormed (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
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
    (currentRelaxedContract (I.freshSuffix first)) .uncapped (zeroNormalAccounting (I.freshSuffix first))
    targetRule sample.1 _ _ targetPrefix htargetHalt hallWritten
  refine ⟨k, htargetHalt, ?_⟩
  apply (prefix_success_iff_physical (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ targetPrefix).mpr
  exact ⟨hfinished, htargetAbandoned, fun stage => (finalOutput_correct_iff _ stage).mpr (hcorrect stage)⟩

noncomputable def runPenaltyCharge (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (penalty : ℝ≥0∞) (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact runObservationBill input C mode accounting rule sample +
    if runSuccess input C mode accounting rule sample then 0 else penalty

/-- The one original eventual-failure penalty dominates the real suffix
penalty pathwise, while the paid observation term is exactly preserved.
Infinite penalties and null-event paths require no special convention. -/
theorem replayedSuffix_penaltyCharge_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample)
    (penalty : ℝ≥0∞) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
    runPenaltyCharge (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule penalty targetSample ≤
      historyComparisonCharge input C mode accounting rule start penalty sample := by
  classical
  dsimp only
  unfold runPenaltyCharge
  rw [replayedSuffix_observationBill_eq input C hearly hcurrent mode accounting rule hlegal sample first start hentry,
    historyComparisonCharge]
  apply add_le_add le_rfl
  by_cases hs : runSuccess input C mode accounting rule sample
  · have ht := replayedSuffix_runSuccess input C hearly hcurrent mode accounting rule hlegal sample first start hentry hs
    simp only [hs, ht, ↓reduceIte, le_refl]
  · simp only [hs, ↓reduceIte]
    split
    · exact bot_le
    · exact le_rfl

end PaperProofs.Common.Native
