module

public import PaperProofs.Common.ReferenceController
public import PaperProofs.Common.NativeCausality

/-!
Pointwise preservation of the actual reference controller. These proofs use
real Prefix invariants and the unchanged visible rule; no world/truth oracle
is added to the executable code. Risk, costs, and cap certificates are outside
this module's scope.

All missing phase branches and the original ReferenceControllerAlignment
are proved below. The proof covers every finite Prefix, including aborted
ones, and every truth/tape with an arbitrary seed universe. The separate
infinite-rank zero-observation and risk targets remain outside this result.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

/-- An unopened future stage has no report, commitment, or execution on every
actual Prefix. This follows from the protocol's genuine-ledger invariant. -/
theorem prefix_future_port_clean (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (stage : I.Stage) (hfuture : s.cursor < stage.val) :
    s.ledger.written stage = none ∧ s.ledger.reportTime stage = none ∧
      (∀ a ∈ s.ledger.commitments, a.handle.stage ≠ stage) ∧
      (∀ e ∈ s.ledger.executions, e.handle.stage ≠ stage) := by
  have hcursor := prefix_cursorInvariant input C mode accounting policy seed truth tapes hp
  have hinv := prefix_invariant input C mode accounting policy seed truth tapes hp
  have hw := hcursor.future_written stage hfuture
  refine ⟨hw, ?_, ?_, ?_⟩
  · cases hr : s.ledger.reportTime stage with
    | none => rfl
    | some time => exact (hinv.report_written stage time hr hw).elim
  · intro a ha
    exact hinv.commitment_ne_open hw ha
  · intro e he
    exact hinv.execution_ne_open hw he

/-- The actual write/report pair stores the old write serial, not report time. -/
theorem prefix_written_report_packet (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (stage : I.Stage) (hwritten : s.ledger.written stage ≠ none)
    (hreported : s.ledger.reportTime stage ≠ none) :
    ∃ bit, historyWrite s.history stage = some (bit, s.ledger.writeSerial stage) ∧
      historyReport s.history stage = some (s.ledger.truth stage, s.ledger.writeSerial stage) ∧
      s.ledger.written stage = some bit := by
  have hbit := prefix_historyWritten input C mode accounting policy seed truth tapes hp stage
  have hserial := prefix_historyWriteSerial input C mode accounting policy seed truth tapes hp stage
  cases hw : historyWrite s.history stage with
  | none =>
    simp only [historyWritten, hw, Option.map_none] at hbit
    exact (hwritten hbit.symm).elim
  | some pair =>
    obtain ⟨bit, serial⟩ := pair
    have hs : serial = s.ledger.writeSerial stage := by
      simpa only [historyWriteSerial, hw, Option.map_some, Option.getD_some] using hserial
    subst serial
    refine ⟨bit, rfl, ?_, ?_⟩
    · rw [prefix_historyReport_early input C hearly mode accounting policy seed truth tapes hp stage]
      cases hr : s.ledger.reportTime stage with
      | none => exact (hreported hr).elim
      | some time => rfl
    · simpa only [historyWritten, hw, Option.map_some] using hbit.symm

/-- A genuine visible handle is recovered exactly from its observed old serial. -/
theorem prefix_visibleHandle_of_valid (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (handle : MismatchHandle I) (hvalid : validHandle s handle) :
    referenceVisibleHandle s.history handle.stage = some handle := by
  obtain ⟨time, hr⟩ := hvalid.2.2
  have hwritten : s.ledger.written handle.stage ≠ none := by rw [hvalid.1]; simp
  have hreported : s.ledger.reportTime handle.stage ≠ none := by rw [hr]; simp
  obtain ⟨bit, hw, _, _⟩ := prefix_written_report_packet input C hearly mode accounting policy seed truth tapes hp
    handle.stage hwritten hreported
  simp only [referenceVisibleHandle, hw, Option.bind_eq_bind, Option.bind_some]
  congr 1
  cases handle with
  | mk stage serial =>
    simp only [MismatchHandle.mk.injEq, true_and]
    exact hvalid.2.1.symm

theorem prefix_historyValidHandle_of_valid (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (handle : MismatchHandle I) (hvalid : validHandle s handle) :
    historyValidHandle s.history handle := by
  obtain ⟨time, hr⟩ := hvalid.2.2
  simp only [historyValidHandle, prefix_historyReport_early input C hearly mode accounting policy seed truth tapes hp handle.stage,
    hr, Option.map_some, prefix_historyWritten input C mode accounting policy seed truth tapes hp handle.stage,
    prefix_historyWriteSerial input C mode accounting policy seed truth tapes hp handle.stage]
  exact ⟨hvalid.1, hvalid.2.1, hvalid.2.1.symm⟩

private theorem replay_extend (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache nextCache : ReferenceReplayCache I)
    (event : VisibleEvent I)
    (hparse : referenceAvailableReplay input initialAvailable budget history = some cache)
    (hstep : referenceAvailableStep input initialAvailable budget cache event = some nextCache)
    (hfinal : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = history ++ [event]) :
    referenceAvailableReplay input initialAvailable budget (history ++ [event]) = some nextCache := by
  have hs := referenceAvailableReplay_some_spec input initialAvailable budget history cache hparse
  have hfold : (history ++ [event]).foldlM (referenceAvailableStep input initialAvailable budget)
      (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  simp only [referenceAvailableReplay, hs.1]
  rw [hfold]
  exact ite_eq_left hfinal

private theorem historyCursor_append_noAdvance (history : List (VisibleEvent I))
    (event : VisibleEvent I) (hnone : eventAdvance event = none) :
    historyCursor (history ++ [event]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, hnone]

private theorem historyUsed_append_noCommitment (history : List (VisibleEvent I))
    (event : VisibleEvent I) (hnone : eventCommitment event = none) :
    historyUsed (history ++ [event]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, hnone]

private theorem replayCorrect_append_unrelated (cache : ReferenceReplayCache I)
    (event : VisibleEvent I) (phase : ReferenceReplayPhase I) (stage : I.Stage)
    (hw : eventWrite stage event = none) (hr : eventReport stage event = none) :
    referenceReplayCorrect {cache with seen := cache.seen ++ [event], phase := phase} stage =
      referenceReplayCorrect cache stage := by
  simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, hw, hr]

theorem referenceReplayMismatch_stage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (handle : MismatchHandle I) (hm : referenceReplayMismatch cache stage handle = true) : handle.stage = stage := by
  cases hw : historyWrite cache.seen stage with
  | none => simp [referenceReplayMismatch, hw] at hm
  | some written =>
    cases hr : historyReport cache.seen stage with
    | none => simp [referenceReplayMismatch, hw, hr] at hm
    | some reported =>
      have hh : written.1 ≠ reported.1 ∧ handle.stage = stage ∧
          handle.writeSerial = written.2 ∧ reported.2 = written.2 := by
        simpa only [referenceReplayMismatch, hw, hr, decide_eq_true_eq] using hm
      exact hh.2.1

private theorem historyUsed_append_commitment (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool) :
    historyUsed (history ++ [.committed handle tool]) = insert tool (historyUsed history) := by
  simp [historyUsed, historyCommitments, List.filterMap_append, eventCommitment, Finset.union_comm]

/-- Allocation preservation uses an actual native Step and the original
entry-snapshot maximizer. It does not posit successful reference execution. -/
theorem referenceStateAligned_allocate (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (hphase : cache.phase = .reported) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (handle : MismatchHandle I) (tool : I.Tool)
    (hmismatch : referenceReplayMismatch cache stage handle = true)
    (hpick : referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) = some tool)
    (current : ℚ) (hcurrent : referenceReplayRisk budget cache = some current)
    (hstep : Step input C .uncapped accounting tapes s (.allocate handle tool) nextState) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | allocate handle tool active valid compatible unused unallocated window resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.committed handle tool]
      phase := .allocated tool }
    have hs := referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans active
    have hstage := referenceStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hhandleStage := referenceReplayMismatch_stage cache stage handle hmismatch
    have hpickSpec := (referenceAvailableRepairTool_spec I initialAvailable stage (historyUsed cache.entryHistory) tool hpick).1
    have hmem : tool ∈ initialAvailable := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpickSpec).2).1
    have hnotEntry : tool ∉ historyUsed cache.entryHistory := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpickSpec).2).2
    have hentry : historyUsed cache.entryHistory = historyUsed cache.seen := by
      simpa only [referenceEntryToolsFit, hphase] using haligned.entry_tools
    have hnot : tool ∉ historyUsed cache.seen := hentry ▸ hnotEntry
    have hcompat : tool ∈ I.eligible stage := hhandleStage ▸ compatible
    have hparser : referenceAvailableStep input initialAvailable budget cache (.committed handle tool) = some nextCache := by
      simp [referenceAvailableStep, hh, hstage, hcurrent, hphase, hmismatch, hcompat, hnot, hmem, hpick, nextCache]
    have hcur : historyCursor nextCache.seen = historyCursor cache.seen :=
      historyCursor_append_noAdvance cache.seen (.committed handle tool) rfl
    have hparse := replay_extend input initialAvailable budget s.history cache nextCache (.committed handle tool)
      haligned.parsed hparser ⟨by simp [nextCache], hs.2.2.2.1, hcur ▸ hs.2.2.2.2.1,
        congrArg (fun seen => seen ++ [.committed handle tool]) haligned.seen⟩
    have hfields := haligned.current_fields stage hcursor
    simp only [hphase, referenceCurrentLedgerFits] at hfields
    have hwf := prefix_ledgerWellFormed input C .uncapped accounting policy seed truth tapes hp
    have hexUnused : ∀ e ∈ s.ledger.executions, e.tool ≠ tool := by
      intro e he heq
      obtain ⟨a, ha, _, hatool, _⟩ := hwf.backed e he
      exact unused a ha (hatool.trans heq)
    refine ⟨nextCache, ?_⟩
    constructor
    · exact hparse
    · exact congrArg (fun seen => seen ++ [.committed handle tool]) haligned.seen
    · exact hh
    · exact hcur.trans haligned.cursor
    · simpa only [nextCache, record, referencePhaseReportCount, hphase] using haligned.trace_count
    · intro ht
      cases ht
    · intro currentStage hc
      have heq : currentStage = stage := Fin.ext (hc.symm.trans hcursor)
      subst currentStage
      refine ⟨handle, hhandleStage, ?_, hcompat, ?_, hexUnused, hfields.2.2.2⟩
      · exact valid
      · exact ⟨⟨handle, tool, s.clock⟩, by simp [record, allocateLedger], rfl, rfl⟩
    · simp only [referenceEntryToolsFit, nextCache, historyUsed_append_commitment]
      exact ⟨congrArg (insert tool) hentry, hnotEntry⟩
    · intro _ currentStage hc
      obtain ⟨kind, entryRisk, hk, hv, hu⟩ := haligned.reported_update (by simp [hphase, referencePhaseReportCount]) currentStage hc
      refine ⟨kind, entryRisk, ?_, hv, ?_⟩
      · simpa only [nextCache, referenceAvailableKind, referenceReplayStage, hcur] using hk
      · have hcorrect := replayCorrect_append_unrelated cache (.committed handle tool) (.allocated tool) currentStage rfl rfl
        simpa only [nextCache, referenceReplayRisk, hcorrect] using hu
    · intro _ _
      exact ⟨current, hcurrent⟩

theorem referenceStateAligned_execute (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s nextState : State I} (initialAvailable : Finset I.Tool) (budget : ℚ)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) (handle : MismatchHandle I) (tool : I.Tool)
    (hphase : cache.phase = .allocated tool) (hmismatch : referenceReplayMismatch cache stage handle = true)
    (hstep : Step input C .uncapped accounting tapes s (.execute handle tool) nextState) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.executed handle tool]
      phase := .executed tool }
    have hs := referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans active
    have hstage := referenceStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hhandleStage := referenceReplayMismatch_stage cache stage handle hmismatch
    have hparser : referenceAvailableStep input initialAvailable budget cache (.executed handle tool) = some nextCache := by
      simp [referenceAvailableStep, hh, hstage, hphase, hmismatch, nextCache]
    have hcur : historyCursor nextCache.seen = historyCursor cache.seen :=
      historyCursor_append_noAdvance cache.seen (.executed handle tool) rfl
    have hparse := replay_extend input initialAvailable budget s.history cache nextCache (.executed handle tool)
      haligned.parsed hparser ⟨by simp [nextCache], hs.2.2.2.1, hcur ▸ hs.2.2.2.2.1,
        congrArg (fun seen => seen ++ [.executed handle tool]) haligned.seen⟩
    refine ⟨nextCache, ?_⟩
    constructor
    · exact hparse
    · exact congrArg (fun seen => seen ++ [.executed handle tool]) haligned.seen
    · exact hh
    · exact hcur.trans haligned.cursor
    · simpa only [nextCache, record, referencePhaseReportCount, hphase] using haligned.trace_count
    · intro ht
      cases ht
    · intro currentStage hc
      have heq : currentStage = stage := Fin.ext (hc.symm.trans hcursor)
      subst currentStage
      refine ⟨?_, ⟨handle, tool, s.clock⟩, by simp [record, executeLedger], hhandleStage, rfl⟩
      have hw := valid.1
      rw [hhandleStage] at hw
      rw [show (record accounting s (.execute handle tool) [.executed handle tool]
        (executeLedger s handle tool) s.cursor false).ledger.written stage = s.ledger.written stage from rfl, hw]
      simp
    · have hused := historyUsed_append_noCommitment cache.seen (.executed handle tool) rfl
      simpa only [referenceEntryToolsFit, nextCache, hused, hphase] using haligned.entry_tools
    · intro _ currentStage hc
      obtain ⟨kind, entryRisk, hk, hv, hu⟩ := haligned.reported_update (by simp [hphase, referencePhaseReportCount]) currentStage hc
      refine ⟨kind, entryRisk, ?_, hv, ?_⟩
      · simpa only [nextCache, referenceAvailableKind, referenceReplayStage, hcur] using hk
      · have hcorrect := replayCorrect_append_unrelated cache (.executed handle tool) (.executed tool) currentStage rfl rfl
        simpa only [nextCache, referenceReplayRisk, hcorrect] using hu
    · intro _ _
      exact haligned.correction_risk tool (Or.inl hphase)

/-- Advancing opens the next stage only after its actual-prefix future port
has been shown clean. No correctness assumption is imposed on old outputs. -/
theorem referenceStateAligned_advance (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hphase : (cache.phase = .reported ∧ referenceReplayCorrect cache stage = true) ∨
      ∃ tool, cache.phase = .executed tool)
    (current : ℚ) (hcurrent : referenceReplayRisk budget cache = some current)
    (hstep : Step input C .uncapped accounting tapes s (.advance stage) nextState) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | advance stage live written resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.advanced stage]
      entryHistory := cache.seen ++ [.advanced stage]
      phase := .testing }
    have hs := referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans live.1
    have hstage := referenceStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hcount : referencePhaseReportCount cache.phase = 1 := by
      rcases hphase with ⟨hphase, _⟩ | ⟨tool, hphase⟩ <;> simp [hphase, referencePhaseReportCount]
    have hparser : referenceAvailableStep input initialAvailable budget cache (.advanced stage) = some nextCache := by
      simp [referenceAvailableStep, hh, hstage, hcurrent, hphase, nextCache]
    have hcur : historyCursor nextCache.seen = historyCursor cache.seen + 1 := by
      simp [nextCache, historyCursor, List.filterMap_append, eventAdvance]
    have hbound : s.cursor + 1 ≤ I.stageCount := by
      have hs : stage.val < I.stageCount := stage.isLt
      omega
    have hparse := replay_extend input initialAvailable budget s.history cache nextCache (.advanced stage)
      haligned.parsed hparser ⟨by simp [nextCache], hs.2.2.2.1,
        by simpa only [hcur, haligned.cursor] using hbound,
        congrArg (fun seen => seen ++ [.advanced stage]) haligned.seen⟩
    refine ⟨nextCache, ?_⟩
    constructor
    · exact hparse
    · exact congrArg (fun seen => seen ++ [.advanced stage]) haligned.seen
    · exact hh
    · exact hcur.trans (congrArg (fun cursor => cursor + 1) haligned.cursor)
    · have htrace := haligned.trace_count
      rw [hcount] at htrace
      simpa only [nextCache, record, referencePhaseReportCount, Nat.add_zero] using htrace
    · intro _
      exact ⟨current, hcurrent⟩
    · intro currentStage hc
      have hfuture : s.cursor < currentStage.val := by
        change s.cursor + 1 = currentStage.val at hc
        omega
      exact prefix_future_port_clean input C .uncapped accounting policy seed truth tapes hp currentStage hfuture
    · rfl
    · intro ht
      cases ht
    · intro tool ht
      rcases ht with ht | ht <;> cases ht

theorem referenceStateAligned_stop (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (hactive : s.halted = false) (hphase : cache.phase = .testing) (hcursor : s.cursor = I.stageCount) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache (stopState s false) := by
  let nextCache : ReferenceReplayCache I := {cache with seen := cache.seen ++ [.stopped], halted := true}
  have hs := referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hc : historyCursor cache.seen = I.stageCount := haligned.cursor.trans hcursor
  have hparser : referenceAvailableStep input initialAvailable budget cache .stopped = some nextCache := by
    simp [referenceAvailableStep, hh, hc, hphase, nextCache]
  have hcur : historyCursor nextCache.seen = historyCursor cache.seen :=
    historyCursor_append_noAdvance cache.seen .stopped rfl
  have hparse := replay_extend input initialAvailable budget s.history cache nextCache .stopped haligned.parsed hparser
    ⟨by simp [nextCache, hphase], hs.2.2.2.1, hcur ▸ hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.stopped]) haligned.seen⟩
  refine ⟨nextCache, ?_⟩
  constructor
  · simpa only [stopState, Bool.false_eq_true, ite_false] using hparse
  · exact congrArg (fun seen => seen ++ [.stopped]) haligned.seen
  · rfl
  · exact hcur.trans haligned.cursor
  · exact haligned.trace_count
  · intro _
    exact haligned.testing_risk hphase
  · intro stage hstage
    have hs : stage.val < I.stageCount := stage.isLt
    change s.cursor = stage.val at hstage
    omega
  · have hused := historyUsed_append_noCommitment cache.seen .stopped rfl
    simpa only [referenceEntryToolsFit, nextCache, hused] using haligned.entry_tools
  · intro ht
    simp only [nextCache, hphase, referencePhaseReportCount] at ht
    contradiction
  · intro tool ht
    simp only [nextCache, hphase] at ht
    rcases ht with ht | ht <;> cases ht

theorem prefix_replayMismatch_of_valid (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (cache : ReferenceReplayCache I) (hseen : cache.seen = s.history)
    (handle : MismatchHandle I) (hvalid : validHandle s handle) :
    referenceReplayMismatch cache handle.stage handle = true := by
  obtain ⟨time, hr⟩ := hvalid.2.2
  have hwritten : s.ledger.written handle.stage ≠ none := by rw [hvalid.1]; simp
  have hreported : s.ledger.reportTime handle.stage ≠ none := by rw [hr]; simp
  obtain ⟨bit, hw, hreport, hb⟩ := prefix_written_report_packet input C hearly mode accounting policy seed truth tapes hp
    handle.stage hwritten hreported
  have hbit : bit = !s.ledger.truth handle.stage := Option.some.inj (hb.symm.trans hvalid.1)
  simp [referenceReplayMismatch, hseen, hw, hreport, hbit, hvalid.2.1]

theorem referenceStateAligned_reported_mismatch (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (hphase : cache.phase = .reported) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hwrong : referenceReplayCorrect cache stage = false) (handle : MismatchHandle I)
    (hvisible : referenceVisibleHandle s.history stage = some handle) :
    validHandle s handle ∧ referenceReplayMismatch cache stage handle = true := by
  have hf := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hf
  obtain ⟨bit, hw, hr, hb⟩ := prefix_written_report_packet input C hearly .uncapped accounting policy seed truth tapes hp
    stage hf.1 hf.2.1
  have hc : referenceReplayCorrect cache stage = decide (bit = s.ledger.truth stage) := by
    simp [referenceReplayCorrect, haligned.seen, hw, hr]
  have hne : bit ≠ s.ledger.truth stage := by
    intro heq
    simp only [hc, heq, decide_true] at hwrong
    contradiction
  have hhandle : handle = ⟨stage, s.ledger.writeSerial stage⟩ := by
    simpa only [referenceVisibleHandle, hw, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] using hvisible.symm
  subst handle
  have hv : validHandle s ⟨stage, s.ledger.writeSerial stage⟩ := by
    refine ⟨hb.trans (congrArg some (Bool.eq_not_iff.mpr hne)), rfl, ?_⟩
    cases ht : s.ledger.reportTime stage with
    | none => exact (hf.2.1 ht).elim
    | some time => exact ⟨time, rfl⟩
  exact ⟨hv, prefix_replayMismatch_of_valid input C hearly .uncapped accounting policy seed truth tapes hp cache haligned.seen _ hv⟩

theorem referenceStateAligned_reported_correct_risk (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (hphase : cache.phase = .reported) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hcorrect : referenceReplayCorrect cache stage = true) :
    ∃ current, referenceReplayRisk budget cache = some current := by
  obtain ⟨kind, entryRisk, _, _, hu⟩ := haligned.reported_update
    (by simp [hphase, referencePhaseReportCount]) stage hcursor
  rw [hcorrect] at hu
  cases kind <;> simp only [referenceBudgetStep, Bool.not_true] at hu
  all_goals exact ⟨_, hu⟩

theorem referenceTestingAction_review_target (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : referenceTestingAction input initialAvailable budget limit cache stage = .review stage) :
    (referenceAvailableCacheTarget I initialAvailable budget cache).isSome := by
  cases ht : referenceAvailableCacheTarget I initialAvailable budget cache with
  | some target => rfl
  | none =>
    cases hk : referenceAvailableKind I initialAvailable cache with
    | none => simp [referenceTestingAction, hk] at haction
    | some kind => cases kind <;> simp [referenceTestingAction, hk, ht] at haction

/-- Preservation follows the actual seed/history rule at every real Step,
including truncation or abandonment. It is independent of eventual success. -/
theorem referenceStateAligned_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input initialAvailable budget limit) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input initialAvailable budget cache s)
    (hstep : Step input C .uncapped accounting tapes s
      (referenceRule input initialAvailable budget limit seed s.history) nextState) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache nextState := by
  have hactive := step_source_active input C .uncapped accounting tapes hstep
  have habandon : referenceRule input initialAvailable budget limit seed s.history = .abandon →
      ∃ nextCache, ReferenceStateAligned input initialAvailable budget nextCache nextState := by
    intro ha
    have hs := hstep
    rw [ha] at hs
    have heq := step_deterministic input C .uncapped accounting tapes hs (.abandon s hactive)
    rw [heq]
    exact referenceStateAligned_abandon input initialAvailable budget cache s haligned hactive
  by_cases hallow : historyAllowsAction s.history (referenceCandidateAction input initialAvailable budget limit s.history)
  · have hrule : referenceRule input initialAvailable budget limit seed s.history =
        referenceCandidateAction input initialAvailable budget limit s.history := by
      exact ite_eq_left hallow
    have hh : cache.halted = false := haligned.halted.trans hactive
    by_cases hbound : s.cursor < I.stageCount
    · let stage : I.Stage := ⟨s.cursor, hbound⟩
      have hcursor : s.cursor = stage.val := rfl
      have hstage := referenceStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
      cases hphase : cache.phase with
      | written =>
        exact ((referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed).2.2.1 hphase).elim
      | testing =>
        have ha := referenceRule_testing_eq_of_aligned input C accounting initialAvailable budget limit
          seed truth tapes hp hactive cache haligned hphase stage hcursor
        rcases referenceTestingAction_supported input initialAvailable budget limit cache stage with hreview | ⟨bit, hwrite⟩ | habort
        · have hs := hstep
          rw [ha, hreview] at hs
          obtain ⟨nextCache, result, hs', ha'⟩ := referenceStateAligned_review input C accounting tapes
            initialAvailable budget cache s haligned hphase hactive stage hcursor
            (referenceTestingAction_review_target input initialAvailable budget limit cache stage hreview)
          rw [step_deterministic input C .uncapped accounting tapes hs hs']
          exact ⟨nextCache, ha'⟩
        · have hs := hstep
          rw [ha, hwrite] at hs
          obtain ⟨nextCache, result, hs', ha'⟩ := referenceStateAligned_write input C hearly accounting
            (referenceRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget cache
            haligned hphase hactive stage hcursor bit
          rw [step_deterministic input C .uncapped accounting tapes hs hs']
          exact ⟨nextCache, ha'⟩
        · exact habandon (ha.trans habort)
      | reported =>
        cases hc : referenceReplayCorrect cache stage with
        | true =>
          have ha : referenceRule input initialAvailable budget limit seed s.history = .advance stage := by
            rw [hrule]
            simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hc]
          have hs := hstep
          rw [ha] at hs
          obtain ⟨current, hcurrent⟩ := referenceStateAligned_reported_correct_risk input initialAvailable budget cache s
            haligned hphase stage hcursor hc
          exact referenceStateAligned_advance input C accounting (referenceRule input initialAvailable budget limit)
            seed truth tapes hp initialAvailable budget cache haligned stage hcursor (Or.inl ⟨hphase, hc⟩) current hcurrent hs
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none =>
            apply habandon
            rw [hrule]
            simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hc, hr]
          | some current =>
            cases hv : referenceVisibleHandle s.history stage with
            | none =>
              apply habandon
              rw [hrule]
              simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hc, hr, hv]
            | some handle =>
              cases ht : referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
              | none =>
                apply habandon
                rw [hrule]
                simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hc, hr, hv, ht]
              | some tool =>
                have ha : referenceRule input initialAvailable budget limit seed s.history = .allocate handle tool := by
                  rw [hrule]
                  simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hc, hr, hv, ht]
                have hs := hstep
                rw [ha] at hs
                have hm := (referenceStateAligned_reported_mismatch input C hearly accounting
                  (referenceRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget cache
                  haligned hphase stage hcursor hc handle hv).2
                exact referenceStateAligned_allocate input C accounting (referenceRule input initialAvailable budget limit)
                  seed truth tapes hp initialAvailable budget cache haligned hphase stage hcursor handle tool hm ht current hr hs
      | allocated tool =>
        cases hv : referenceVisibleHandle s.history stage with
        | none =>
          apply habandon
          rw [hrule]
          simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hv]
        | some handle =>
          have ha : referenceRule input initialAvailable budget limit seed s.history = .execute handle tool := by
            rw [hrule]
            simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hv]
          have hs := hstep
          rw [ha] at hs
          obtain ⟨oldHandle, hhs, hvalid, _, _, _, _⟩ := by
            simpa only [hphase, referenceCurrentLedgerFits] using haligned.current_fields stage hcursor
          have hvo := prefix_visibleHandle_of_valid input C hearly .uncapped accounting
            (referenceRule input initialAvailable budget limit) seed truth tapes hp oldHandle hvalid
          rw [hhs] at hvo
          have heq : handle = oldHandle := Option.some.inj (hv.symm.trans hvo)
          subst handle
          have hm := prefix_replayMismatch_of_valid input C hearly .uncapped accounting
            (referenceRule input initialAvailable budget limit) seed truth tapes hp cache haligned.seen oldHandle hvalid
          rw [hhs] at hm
          exact referenceStateAligned_execute input C accounting tapes initialAvailable budget cache haligned
            stage hcursor oldHandle tool hphase hm hs
      | executed tool =>
        have ha : referenceRule input initialAvailable budget limit seed s.history = .advance stage := by
          rw [hrule]
          simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase]
        have hs := hstep
        rw [ha] at hs
        obtain ⟨current, hcurrent⟩ := haligned.correction_risk tool (Or.inr hphase)
        exact referenceStateAligned_advance input C accounting (referenceRule input initialAvailable budget limit)
          seed truth tapes hp initialAvailable budget cache haligned stage hcursor (Or.inr ⟨tool, hphase⟩) current hcurrent hs
    · have hcursor : s.cursor = I.stageCount := by
        have hc := (prefix_cursorInvariant input C .uncapped accounting
          (referenceRule input initialAvailable budget limit) seed truth tapes hp).bound
        omega
      have hs := referenceAvailableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
      have hphase : cache.phase = .testing := by
        cases hc : cache.phase with
        | testing => rfl
        | written => exact (hs.2.2.1 hc).elim
        | reported | allocated tool | executed tool =>
          have ht := haligned.trace_count
          simp only [hc, referencePhaseReportCount] at ht
          omega
      have hstage : referenceReplayStage I cache = none := by
        simp [referenceReplayStage, haligned.cursor, hbound]
      have hhistory : historyCursor s.history = I.stageCount := by
        rw [← haligned.seen, haligned.cursor, hcursor]
      have ha : referenceRule input initialAvailable budget limit seed s.history = .stop := by
        rw [hrule]
        simp [referenceCandidateAction, haligned.parsed, hh, hstage, hhistory]
      have hs' := hstep
      rw [ha] at hs'
      rw [step_deterministic input C .uncapped accounting tapes hs' (.stop s hactive)]
      exact referenceStateAligned_stop input initialAvailable budget cache s haligned hactive hphase hcursor
  · exact habandon (ite_eq_right hallow)

/-- Every actual finite Prefix of the unchanged controller has a replay
cache and ledger alignment, for arbitrary seed type and every truth/tape. -/
theorem prefix_referenceStateAligned {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input initialAvailable budget limit) seed truth tapes n s) :
    ∃ cache, ReferenceStateAligned input initialAvailable budget cache s := by
  induction hp with
  | initial => exact ⟨referenceReplayInitial I, referenceStateAligned_initial input initialAvailable budget hbudget hsmall truth⟩
  | next earlier step ih =>
    obtain ⟨cache, haligned⟩ := ih
    exact referenceStateAligned_step input C hearly accounting initialAvailable budget limit seed truth tapes earlier cache haligned step

private theorem cursor_of_replayStage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage with hb
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

/-- The finite permission guard is nonbinding at any genuinely aligned
Prefix. This is proved from observable queries and actual ledger invariants,
not supplied as a condition on the controller. -/
theorem referenceCandidateAction_allowed_of_aligned {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input initialAvailable budget cache s) :
    historyAllowsAction s.history (referenceCandidateAction input initialAvailable budget limit s.history) := by
  cases hh : cache.halted with
  | true => simp [referenceCandidateAction, haligned.parsed, hh, historyAllowsAction]
  | false =>
    cases hs : referenceReplayStage I cache with
    | none =>
      simp only [referenceCandidateAction, haligned.parsed, hh, Bool.false_eq_true, ite_false, hs]
      split_ifs <;> trivial
    | some stage =>
      have hcursor : s.cursor = stage.val := haligned.cursor.symm.trans (cursor_of_replayStage cache stage hs)
      have hch : historyCursor s.history = stage.val := by rw [← haligned.seen]; exact haligned.cursor.trans hcursor
      cases hphase : cache.phase with
      | testing =>
        have hcand : referenceCandidateAction input initialAvailable budget limit s.history =
            referenceTestingAction input initialAvailable budget limit cache stage := by
          simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase]
        rw [hcand]
        exact referenceTestingAction_allowed_of_aligned input C accounting policy seed truth tapes hp
          initialAvailable budget limit cache haligned hphase stage hcursor
      | written => simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, historyAllowsAction]
      | reported =>
        have hf := haligned.current_fields stage hcursor
        simp only [hphase, referenceCurrentLedgerFits] at hf
        cases hc : referenceReplayCorrect cache stage with
        | true =>
          have hcand : referenceCandidateAction input initialAvailable budget limit s.history = .advance stage := by
            simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hc]
          rw [hcand]
          refine ⟨hch, ?_⟩
          rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
          exact hf.1
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none => simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hc, hr, historyAllowsAction]
          | some current =>
            cases hv : referenceVisibleHandle s.history stage with
            | none => simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hc, hr, hv, historyAllowsAction]
            | some handle =>
              cases ht : referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
              | none => simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hc, hr, hv, ht, historyAllowsAction]
              | some tool =>
                have hcand : referenceCandidateAction input initialAvailable budget limit s.history = .allocate handle tool := by
                  simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hc, hr, hv, ht]
                rw [hcand]
                obtain ⟨hvalid, hm⟩ := referenceStateAligned_reported_mismatch input C hearly accounting policy seed truth tapes hp
                  initialAvailable budget cache haligned hphase stage hcursor hc handle hv
                have hhs := referenceReplayMismatch_stage cache stage handle hm
                have hpick := (referenceAvailableRepairTool_spec I initialAvailable stage (historyUsed cache.entryHistory) tool ht).1
                have hentry : historyUsed cache.entryHistory = historyUsed s.history := by
                  simpa only [referenceEntryToolsFit, hphase, haligned.seen] using haligned.entry_tools
                refine ⟨by simpa only [hhs] using hch,
                  prefix_historyValidHandle_of_valid input C hearly .uncapped accounting policy seed truth tapes hp handle hvalid,
                  ?_, ?_, ?_⟩
                · simpa only [hhs] using (Finset.mem_inter.mp hpick).1
                · rw [← hentry]
                  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpick).2).2
                · intro pair hpair
                  rw [prefix_historyCommitments input C .uncapped accounting policy seed truth tapes hp] at hpair
                  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hpair
                  simpa only [hhs] using hf.2.2.1 a ha
      | allocated tool =>
        cases hv : referenceVisibleHandle s.history stage with
        | none => simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hv, historyAllowsAction]
        | some handle =>
          have hcand : referenceCandidateAction input initialAvailable budget limit s.history = .execute handle tool := by
            simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase, hv]
          rw [hcand]
          obtain ⟨oldHandle, hhs, hvalid, hcompat, hcommitted, hunused, hstageUnused⟩ := by
            simpa only [hphase, referenceCurrentLedgerFits] using haligned.current_fields stage hcursor
          have hvo := prefix_visibleHandle_of_valid input C hearly .uncapped accounting policy seed truth tapes hp oldHandle hvalid
          rw [hhs] at hvo
          have heq : handle = oldHandle := Option.some.inj (hv.symm.trans hvo)
          subst handle
          refine ⟨by simpa only [hhs] using hch,
            prefix_historyValidHandle_of_valid input C hearly .uncapped accounting policy seed truth tapes hp oldHandle hvalid,
            by simpa only [hhs] using hcompat, ?_, ?_, ?_⟩
          · obtain ⟨a, ha, hh, ht⟩ := hcommitted
            rw [prefix_historyCommitments input C .uncapped accounting policy seed truth tapes hp]
            exact List.mem_map.mpr ⟨a, ha, Prod.ext hh ht⟩
          · intro pair hpair
            rw [prefix_historyExecutions input C .uncapped accounting policy seed truth tapes hp] at hpair
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
            exact hunused e he
          · intro pair hpair
            rw [prefix_historyExecutions input C .uncapped accounting policy seed truth tapes hp] at hpair
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
            simpa only [hhs] using hstageUnused e he
      | executed tool =>
        have hcand : referenceCandidateAction input initialAvailable budget limit s.history = .advance stage := by
          simp [referenceCandidateAction, haligned.parsed, hh, hs, hphase]
        rw [hcand]
        refine ⟨hch, ?_⟩
        rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
        have hf := haligned.current_fields stage hcursor
        simp only [hphase, referenceCurrentLedgerFits] at hf
        exact hf.1

/-- Every actual controller Prefix runs its original candidate action;
the visible permission check does not add an abandonment branch. -/
theorem referenceRule_eq_candidate_of_prefix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input initialAvailable budget limit) seed truth tapes n s) :
    referenceRule input initialAvailable budget limit seed s.history =
      referenceCandidateAction input initialAvailable budget limit s.history := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting initialAvailable budget hbudget hsmall
    limit seed truth tapes hp
  exact ite_eq_left (referenceCandidateAction_allowed_of_aligned input C hearly accounting
    (referenceRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget limit cache haligned)

/-- The original all-truth/all-tape alignment target is now a theorem,
uniform in the seed universe, initial available set, budget, and quota. -/
theorem referenceControllerAlignment (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (Seed : Type*) [MeasurableSpace Seed] : ReferenceControllerAlignment input C hearly accounting Seed := by
  intro initialAvailable budget hbudget hsmall limit seed truth tapes n s hp _
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting initialAvailable budget hbudget hsmall
    limit seed truth tapes hp
  refine ⟨cache, haligned.parsed, haligned, ?_⟩
  simp only [decide_eq_true_eq]
  exact referenceCandidateAction_allowed_of_aligned input C hearly accounting
    (referenceUncappedPolicy input C hearly accounting initialAvailable budget limit).rule seed truth tapes hp
    initialAvailable budget limit cache haligned

end PaperProofs.Common.Native
