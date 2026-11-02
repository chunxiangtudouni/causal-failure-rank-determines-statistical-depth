module

public import PaperProofs.Common.PSTR_ST_TableNative_002

/-! Actual table parser/Native Prefix alignment. The table tie is retained;
no generic/table history or run equality is asserted. Scalar and resource
lemmas are reused from the frozen first delivery. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableAlignment

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice

variable {I : Instance}

abbrev tableRepairTool (I : Instance) (available : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) : Option I.Tool :=
  (tableReply I available stage used).tool

theorem tableRepairTool_spec (I : Instance) (hlaminar : LaminarSchedule I.compatibility) (available : Finset I.Tool) (stage : I.Stage)
    (used : Finset I.Tool) (tool : I.Tool)
    (hsel : tableRepairTool I available stage used = some tool) :
    tool ∈ I.eligible stage ∩ (available \ used) ∧
      errorRank (I.compatibility.drop (stage.val + 1)) ((available \ used).erase tool) =
        badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) (available \ used) := by
  have hs := (PSTRCallback.callbackClaims I.toolCount I.compatibility hlaminar).2.1 stage
    ((Finset.univ \ available) ∪ used)
  dsimp only at hs
  have ht := hs.2.2.2 tool hsel
  have hremaining : Finset.univ \ ((Finset.univ \ available) ∪ used) = available \ used := by
    ext x
    simp
  have hmem : tool ∈ available \ used := by
    rw [← hremaining]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht.2.1⟩
  refine ⟨Finset.mem_inter.mpr ⟨ht.1, hmem⟩, ?_⟩
  simpa only [hs.2.1, hremaining, Instance.eligible, List.get_eq_getElem] using ht.2.2

structure TableStateAligned (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I) : Prop where
  parsed : tableReplay input initialAvailable risk s.history = some cache
  seen : cache.seen = s.history
  halted : cache.halted = s.halted
  cursor : historyCursor cache.seen = s.cursor
  trace_count : cache.events.length = s.cursor + referencePhaseReportCount cache.phase
  testing_risk : cache.phase = .testing → ∃ current, referenceReplayRisk risk cache = some current
  current_fields : ∀ stage : I.Stage, s.cursor = stage.val → referenceCurrentLedgerFits cache.phase s stage
  entry_tools : referenceEntryToolsFit cache
  reported_update : referencePhaseReportCount cache.phase = 1 →
    ∀ stage : I.Stage, s.cursor = stage.val →
      ∃ kind entryRisk, tableKind I initialAvailable cache = some kind ∧
        ReferenceBudgetValid entryRisk ∧ referenceReplayRisk risk cache =
          referenceBudgetStep kind (!(referenceReplayCorrect cache stage)) entryRisk
  correction_risk : ∀ tool, cache.phase = .allocated tool ∨ cache.phase = .executed tool →
    ∃ current, referenceReplayRisk risk cache = some current


variable (hlaminar : LaminarSchedule I.compatibility)
include hlaminar

omit hlaminar in
theorem tableReplay_initial (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) :
    tableReplay input initialAvailable risk [] = some (referenceReplayInitial I) := by
  have hr : 0 < risk ∧ risk ≤ 1 / 2 := ⟨hrisk, hsmall⟩
  simp only [tableReplay, hr]
  simp [referenceReplayInitial, historyCursor]

omit hlaminar in
private theorem historyCursor_append_write (history : List (VisibleEvent I))
    (stage : I.Stage) (bit : Bool) (serial : ℕ) :
    historyCursor (history ++ [.wrote stage bit serial]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

omit hlaminar in
private theorem historyCursor_append_write_report (history : List (VisibleEvent I))
    (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    historyCursor (history ++ [.wrote stage bit serial, .report stage truth serial]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

omit hlaminar in
private theorem availableKind_written (I : Instance) (initialAvailable : Finset I.Tool)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : ℕ) :
    tableKind I initialAvailable
      { cache with seen := cache.seen ++ [.wrote stage bit serial], phase := .written } =
        tableKind I initialAvailable cache := by
  simp only [tableKind, referenceReplayStage, historyCursor_append_write]

omit hlaminar in
/-- The complete early packet is replayed as one actual Native write response.
The .written intermediate cache is not asserted to be a Native state. -/
theorem tableReplay_write_packet (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : tableReplay input initialAvailable risk history = some cache)
    (hhalt : cache.halted = false) (hphase : cache.phase = .testing) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) (kind : ReferenceBudgetCase)
    (hkind : tableKind I initialAvailable cache = some kind) (current : ℚ)
    (hcurrent : referenceReplayRisk risk cache = some current) (hlen : cache.events.length < I.stageCount)
    (bit truth : Bool) (serial : ℕ) (hserial : serial = (historyActions cache.seen).length) :
    tableReplay input initialAvailable risk (history ++ [.wrote stage bit serial, .report stage truth serial]) =
      some { cache with
        seen := cache.seen ++ [.wrote stage bit serial, .report stage truth serial]
        events := cache.events ++ [(kind, decide (bit ≠ truth))]
        phase := .reported } := by
  let written : ReferenceReplayCache I :=
    { cache with seen := cache.seen ++ [.wrote stage bit serial], phase := .written }
  let reported : ReferenceReplayCache I :=
    { cache with
      seen := cache.seen ++ [.wrote stage bit serial, .report stage truth serial]
      events := cache.events ++ [(kind, decide (bit ≠ truth))]
      phase := .reported }
  have hw : tableStep input initialAvailable risk cache (.wrote stage bit serial) = some written := by
    simp [tableStep, hhalt, hstage, hkind, hcurrent, hphase, hserial, written]
  have hstage' : referenceReplayStage I written = some stage := by
    simpa only [written, referenceReplayStage, historyCursor_append_write] using hstage
  have hkind' : tableKind I initialAvailable written = some kind := by
    simpa only [written, availableKind_written] using hkind
  have hwrite : historyWrite written.seen stage = some (bit, serial) := by
    simp [written, historyWrite, List.filterMap_append, eventWrite]
  have hr : tableStep input initialAvailable risk written (.report stage truth serial) = some reported := by
    have hhalt' : written.halted = false := hhalt
    have hcurrent' : referenceReplayRisk risk written = some current := hcurrent
    simp only [tableStep, hhalt', Bool.false_eq_true, ite_false]
    simp only [hstage', Option.bind_eq_bind, Option.bind_some, hwrite, hkind', hcurrent']
    rw [ite_eq_left (show True ∧ True ∧ written.phase = .written ∧
      written.events.length < I.stageCount from ⟨trivial, trivial, rfl, hlen⟩)]
    simp only [written, reported, hhalt, List.append_assoc, List.singleton_append]
  have hs := tableReplay_some_spec input initialAvailable risk history cache hparse
  have hfold : (history ++ [VisibleEvent.wrote stage bit serial, VisibleEvent.report stage truth serial]).foldlM
      (tableStep input initialAvailable risk) (referenceReplayInitial I) = some reported := by
    rw [List.foldlM_append, hs.2.1]
    simp [hw, hr]
  have hg : reported.phase ≠ .written ∧ reported.events.length ≤ I.stageCount ∧
      historyCursor reported.seen ≤ I.stageCount ∧
      reported.seen = history ++ [.wrote stage bit serial, .report stage truth serial] := by
    refine ⟨by simp [reported], ?_, ?_, ?_⟩
    · simpa only [reported, List.length_append, List.length_singleton] using Nat.succ_le_of_lt hlen
    · simpa only [reported, historyCursor_append_write_report] using hs.2.2.2.2.1
    · simpa only [reported] using congrArg (fun seen => seen ++ [.wrote stage bit serial, .report stage truth serial]) hs.2.2.2.2.2
  simp only [tableReplay, hs.1]
  rw [hfold]
  exact ite_eq_left hg

omit hlaminar in
theorem tableStateAligned_initial (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) (truth : I.Stage → Bool) :
    TableStateAligned input initialAvailable risk (referenceReplayInitial I) (initial truth) := by
  constructor
  · exact tableReplay_initial input initialAvailable risk hrisk hsmall
  · rfl
  · rfl
  · rfl
  · rfl
  · intro _
    exact ⟨risk / 2, rfl⟩
  · intro stage _
    simp [referenceReplayInitial, referenceCurrentLedgerFits, initial]
  · simp [referenceEntryToolsFit, referenceReplayInitial, historyUsed, historyCommitments]
  · intro hcount
    norm_num [referenceReplayInitial, referencePhaseReportCount] at hcount
  · intro tool hphase
    rcases hphase with hphase | hphase <;> cases hphase

omit hlaminar in
theorem tableStateAligned_stage (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable risk cache s) (stage : I.Stage)
    (hcursor : s.cursor = stage.val) : referenceReplayStage I cache = some stage := by
  have hc : historyCursor cache.seen = stage.val := haligned.cursor.trans hcursor
  have hs : stage.val < I.stageCount := stage.isLt
  simp [referenceReplayStage, hc, hs]

omit hlaminar in
theorem tableTestingAction_allowed_of_aligned (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I)  (policy : PolicyRule I Unit) (seed : Unit)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    historyAllowsAction s.history (tableTestingAction input initialAvailable risk limit cache stage) := by
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hw : historyWritten s.history stage = none := by
    rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
    exact hfields.1
  have hc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp).trans hcursor
  rcases tableTestingAction_supported input initialAvailable risk limit cache stage with hreview | ⟨bit, hwrite⟩ | habandon
  · rw [hreview]
    exact ⟨hc, hw⟩
  · rw [hwrite]
    exact ⟨hc, hw⟩
  · rw [habandon]
    trivial

omit hlaminar in
/-- The finite Native permission guard is nonbinding in an aligned testing
state. The all-prefix alignment induction is not assumed to be complete. -/
theorem tableRule_testing_eq_of_aligned  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input initialAvailable risk limit) seed truth tapes n s)
    (hactive : s.halted = false) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    tableRule input initialAvailable risk limit seed s.history =
      tableTestingAction input initialAvailable risk limit cache stage := by
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hs := tableStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hc : tableCandidate input initialAvailable risk limit s.history =
      tableTestingAction input initialAvailable risk limit cache stage := by
    simp only [tableCandidate, haligned.parsed, hh, Bool.false_eq_true, ite_false, hs, hphase]
  have hallow := tableTestingAction_allowed_of_aligned input C accounting
    (tableRule input initialAvailable risk limit) seed truth tapes hp initialAvailable risk limit cache haligned hphase stage hcursor
  simp only [tableRule, hc, ite_eq_left hallow]

theorem tableStateAligned_testing_ready (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    ∃ kind current, tableKind I initialAvailable cache = some kind ∧
      referenceReplayRisk risk cache = some current ∧ ReferenceBudgetValid current ∧ cache.events.length < I.stageCount := by
  have hstage := tableStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  obtain ⟨kind, hk⟩ := referenceAvailableRankCase_exists I initialAvailable stage (historyUsed cache.entryHistory)
  have hkind : tableKind I initialAvailable cache = some kind := by
    rw [(callbackFormulaClaims I hlaminar initialAvailable cache risk).1]
    simp [referenceAvailableKind, hstage, hk]
  obtain ⟨current, hcurrent⟩ := haligned.testing_risk hphase
  have hs := tableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hstart : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  have hvalid := (referenceBudgetPath_valid_floor cache.events (risk / 2) current hstart hcurrent).1
  have hcount : cache.events.length = s.cursor := by
    simpa only [hphase, referencePhaseReportCount, Nat.add_zero] using haligned.trace_count
  have hbound : s.cursor < I.stageCount := hcursor ▸ stage.isLt
  exact ⟨kind, current, hkind, hcurrent, hvalid, hcount.trans_lt hbound⟩

/-- An aligned testing state has a real lawful write successor, and its full
early response packet is accepted by the same availability-aware replay.
This closes that parser branch, without assuming a performance guarantee. -/
theorem tableStateAligned_write_replay (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) 
    (policy : PolicyRule I Unit) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val) (bit : Bool) :
    ∃ kind nextCache,
      Step input C .uncapped accounting tapes s (.write stage bit)
        (record accounting s (.write stage bit) (writeResponses C s stage bit)
          (reportedWriteLedger C s stage bit) s.cursor false) ∧
      tableReplay input initialAvailable risk
        (record accounting s (.write stage bit) (writeResponses C s stage bit)
          (reportedWriteLedger C s stage bit) s.cursor false).history = some nextCache ∧
      nextCache.phase = .reported ∧
      nextCache.events = cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))] := by
  obtain ⟨kind, current, hkind, hcurrent, _, hlen⟩ :=
    tableStateAligned_testing_ready hlaminar input initialAvailable risk cache s haligned hphase stage hcursor
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := tableStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hserial : s.clock = (historyActions cache.seen).length := by
    rw [haligned.seen]
    exact (prefix_historyActions_length input C .uncapped accounting policy seed truth tapes hp).symm
  have hpacket := tableReplay_write_packet input initialAvailable risk s.history cache haligned.parsed
    hh hphase stage hstage kind hkind current hcurrent hlen bit (s.ledger.truth stage) s.clock hserial
  let nextCache : ReferenceReplayCache I := { cache with
    seen := cache.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
    events := cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
    phase := .reported }
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  refine ⟨kind, nextCache, .write s stage bit ⟨hactive, hcursor⟩ hfields.1 (.inl rfl), ?_, rfl, rfl⟩
  simpa only [record, writeResponses, hearly, ite_true, writeLedger, nextCache, List.singleton_append] using hpacket

omit hlaminar in
private theorem historyCursor_append_abandon (history : List (VisibleEvent I)) :
    historyCursor (history ++ [.abandoned]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, eventAdvance]

omit hlaminar in
private theorem historyUsed_append_abandon (history : List (VisibleEvent I)) :
    historyUsed (history ++ [.abandoned]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

omit hlaminar in
private theorem availableKind_abandoned (I : Instance) (initialAvailable : Finset I.Tool)
    (cache : ReferenceReplayCache I) :
    tableKind I initialAvailable { cache with seen := cache.seen ++ [.abandoned], halted := true } =
      tableKind I initialAvailable cache := by
  simp only [tableKind, referenceReplayStage, historyCursor_append_abandon]

omit hlaminar in
private theorem replayCorrect_abandoned (cache : ReferenceReplayCache I) (stage : I.Stage) :
    referenceReplayCorrect { cache with seen := cache.seen ++ [.abandoned], halted := true } stage =
      referenceReplayCorrect cache stage := by
  simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons, eventWrite, eventReport]

omit hlaminar in
private theorem currentLedgerFits_stop (phase : ReferenceReplayPhase I) (s : State I) (stage : I.Stage) (abandon : Bool) :
    referenceCurrentLedgerFits phase (stopState s abandon) stage ↔ referenceCurrentLedgerFits phase s stage := by
  cases phase <;> rfl

omit hlaminar in
/-- Abandonment preserves the alignment, including a reported no-tool failure
whose continuation budget is none. It retains every previously paid charge. -/
theorem tableStateAligned_abandon (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable risk cache s) (hactive : s.halted = false) :
    ∃ nextCache, TableStateAligned input initialAvailable risk nextCache (stopState s true) := by
  let nextCache : ReferenceReplayCache I := { cache with seen := cache.seen ++ [.abandoned], halted := true }
  have hs := tableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstep : tableStep input initialAvailable risk cache .abandoned = some nextCache := by
    simp [tableStep, hh, hs.2.2.1, nextCache]
  have hfold : (s.history ++ [VisibleEvent.abandoned]).foldlM (tableStep input initialAvailable risk)
      (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  have hg : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = s.history ++ [.abandoned] := by
    exact ⟨hs.2.2.1, hs.2.2.2.1, by simpa only [nextCache, historyCursor_append_abandon] using hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.abandoned]) haligned.seen⟩
  have hparse : tableReplay input initialAvailable risk (stopState s true).history = some nextCache := by
    simp only [tableReplay, hs.1, stopState, ite_true]
    rw [hfold]
    exact ite_eq_left hg
  refine ⟨nextCache, ?_⟩
  constructor
  · exact hparse
  · simpa only [nextCache, stopState, ite_true] using congrArg (fun seen => seen ++ [.abandoned]) haligned.seen
  · rfl
  · simpa only [nextCache, stopState, historyCursor_append_abandon] using haligned.cursor
  · exact haligned.trace_count
  · intro hphase
    exact haligned.testing_risk hphase
  · intro stage hcursor
    exact (currentLedgerFits_stop cache.phase s stage true).mpr (haligned.current_fields stage hcursor)
  · simpa only [referenceEntryToolsFit, nextCache, historyUsed_append_abandon] using haligned.entry_tools
  · intro hcount stage hcursor
    obtain ⟨kind, entryRisk, hk, hv, hu⟩ := haligned.reported_update hcount stage hcursor
    refine ⟨kind, entryRisk, ?_, hv, ?_⟩
    · simpa only [nextCache, availableKind_abandoned] using hk
    · simpa only [nextCache, referenceReplayRisk, replayCorrect_abandoned] using hu
  · intro tool hphase
    exact haligned.correction_risk tool hphase

omit hlaminar in
private theorem historyCursor_append_observation (history : List (VisibleEvent I))
    (stage : I.Stage) (symbol : ℕ) :
    historyCursor (history ++ [.observation stage symbol]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

omit hlaminar in
private theorem historyUsed_append_observation (history : List (VisibleEvent I))
    (stage : I.Stage) (symbol : ℕ) :
    historyUsed (history ++ [.observation stage symbol]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

omit hlaminar in
private theorem currentLedgerFits_review (phase : ReferenceReplayPhase I)
    (accounting : NormalAccounting I) (s : State I) (stage current : I.Stage) (symbol : ℕ) :
    referenceCurrentLedgerFits phase
      (record accounting s (.review stage) [.observation stage symbol]
        (reviewLedger s stage) s.cursor false) current ↔ referenceCurrentLedgerFits phase s current := by
  cases phase <;> rfl

omit hlaminar in
/-- A genuine review consumes precisely the next tape symbol and preserves
the testing invariant. Its target-isSome obligation is explicit here; it
will be obtained from the actual testing action in the full Prefix proof. -/
theorem tableStateAligned_review (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false) (stage : I.Stage)
    (hcursor : s.cursor = stage.val)
    (htarget : (tableTarget I initialAvailable risk cache).isSome) :
    ∃ nextCache nextState,
      Step input C .uncapped accounting tapes s (.review stage) nextState ∧
      TableStateAligned input initialAvailable risk nextCache nextState := by
  let symbol := tapes stage (s.ledger.reviews stage).toNat
  let nextCache : ReferenceReplayCache I := { cache with seen := cache.seen ++ [.observation stage symbol.val] }
  let nextState : State I := record accounting s (.review stage) [.observation stage symbol.val]
    (reviewLedger s stage) s.cursor false
  have hs := tableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := tableStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hport : s.ledger.written stage = none := by
    exact hfields.1
  have hstep : tableStep input initialAvailable risk cache (.observation stage symbol.val) = some nextCache := by
    have halphabet : symbol.val < (input.experiment stage).alphabetSize := symbol.isLt
    simp [tableStep, hh, hstage, hphase, halphabet, htarget, nextCache]
  have hfold : (s.history ++ [VisibleEvent.observation stage symbol.val]).foldlM
      (tableStep input initialAvailable risk) (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  have hg : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = nextState.history := by
    exact ⟨hs.2.2.1, hs.2.2.2.1,
      by simpa only [nextCache, historyCursor_append_observation] using hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.observation stage symbol.val]) haligned.seen⟩
  have hparse : tableReplay input initialAvailable risk nextState.history = some nextCache := by
    simp only [tableReplay, hs.1, nextState, record]
    rw [hfold]
    exact ite_eq_left hg
  refine ⟨nextCache, nextState, .review s stage ⟨hactive, hcursor⟩ hport (.inl rfl), ?_⟩
  constructor
  · exact hparse
  · exact congrArg (fun seen => seen ++ [.observation stage symbol.val]) haligned.seen
  · exact hh
  · simpa only [nextCache, nextState, record, historyCursor_append_observation] using haligned.cursor
  · exact haligned.trace_count
  · intro _
    exact haligned.testing_risk hphase
  · intro current hcurrent
    exact (currentLedgerFits_review cache.phase accounting s stage current symbol.val).mpr (haligned.current_fields current hcurrent)
  · simpa only [referenceEntryToolsFit, nextCache, historyUsed_append_observation] using haligned.entry_tools
  · intro hcount
    simp only [nextCache, hphase, referencePhaseReportCount] at hcount
    contradiction
  · intro tool hcorrection
    simp only [nextCache, hphase] at hcorrection
    rcases hcorrection with h | h <;> cases h

omit hlaminar in
private theorem budgetPath_append (initial : ℚ) (events tail : List ReferenceBudgetEvent) :
    referenceBudgetPath initial (events ++ tail) =
      (referenceBudgetPath initial events).bind (fun current => referenceBudgetPath current tail) := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.cons_append, referenceBudgetPath]
    cases hstep : referenceBudgetStep event.1 event.2 initial with
    | none => rfl
    | some child => simpa only [Option.bind_some] using ih child

omit hlaminar in
private theorem historyUsed_append_write_report (history : List (VisibleEvent I))
    (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    historyUsed (history ++ [.wrote stage bit serial, .report stage truth serial]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

/-- Full alignment after an actual early write/report packet. The budget
case is computed from the unchanged entry snapshot, before any commitment.
An unrepairable error is allowed to produce none in this reported phase. -/
theorem tableStateAligned_write (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) 
    (policy : PolicyRule I Unit) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val) (bit : Bool) :
    ∃ nextCache nextState,
      Step input C .uncapped accounting tapes s (.write stage bit) nextState ∧
      TableStateAligned input initialAvailable risk nextCache nextState := by
  obtain ⟨kind, current, hkind, hcurrent, hvalid, hlen⟩ :=
    tableStateAligned_testing_ready hlaminar input initialAvailable risk cache s haligned hphase stage hcursor
  let nextCache : ReferenceReplayCache I := { cache with
    seen := cache.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
    events := cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
    phase := .reported }
  let nextState : State I := record accounting s (.write stage bit) (writeResponses C s stage bit)
    (reportedWriteLedger C s stage bit) s.cursor false
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := tableStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hserial : s.clock = (historyActions cache.seen).length := by
    rw [haligned.seen]
    exact (prefix_historyActions_length input C .uncapped accounting policy seed truth tapes hp).symm
  have hpacket := tableReplay_write_packet input initialAvailable risk s.history cache haligned.parsed
    hh hphase stage hstage kind hkind current hcurrent hlen bit (s.ledger.truth stage) s.clock hserial
  have hparse : tableReplay input initialAvailable risk nextState.history = some nextCache := by
    simpa only [record, writeResponses, hearly, ite_true, writeLedger, nextCache, nextState,
      List.singleton_append] using hpacket
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hcorrect : referenceReplayCorrect nextCache stage = decide (bit = s.ledger.truth stage) := by
    simp [referenceReplayCorrect, nextCache, historyWrite, historyReport, List.filterMap_append,
      List.filterMap_cons, eventWrite, eventReport]
  have hnextKind : tableKind I initialAvailable nextCache = some kind := by
    simpa only [nextCache, tableKind, referenceReplayStage,
      historyCursor_append_write_report] using hkind
  have hnextRisk : referenceReplayRisk risk nextCache =
      referenceBudgetStep kind (!(referenceReplayCorrect nextCache stage)) current := by
    rw [hcorrect]
    simp only [referenceReplayRisk, nextCache, budgetPath_append, referenceBudgetPath]
    change (referenceReplayRisk risk cache).bind
      (fun child => (referenceBudgetStep kind (decide (bit ≠ s.ledger.truth stage)) child).bind some) = _
    rw [hcurrent]
    simp
  refine ⟨nextCache, nextState, .write s stage bit ⟨hactive, hcursor⟩ hfields.1 (.inl rfl), ?_⟩
  constructor
  · exact hparse
  · simpa only [nextCache, nextState, record, writeResponses, hearly, ite_true, writeLedger,
      List.singleton_append] using congrArg
        (fun seen => seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]) haligned.seen
  · exact hh
  · simpa only [nextCache, nextState, record, historyCursor_append_write_report] using haligned.cursor
  · have hcount := haligned.trace_count
    simp only [hphase, referencePhaseReportCount, Nat.add_zero] at hcount
    simpa only [nextCache, nextState, record, List.length_append, List.length_singleton,
      referencePhaseReportCount] using congrArg (fun count => count + 1) hcount
  · intro htesting
    cases htesting
  · intro currentStage hcurrentCursor
    have heq : currentStage = stage := Fin.ext (hcurrentCursor.symm.trans hcursor)
    subst currentStage
    simp only [nextCache, referenceCurrentLedgerFits, nextState, record, reportedWriteLedger,
      hearly, ite_true, writeLedger, Function.update_self]
    exact ⟨by simp, by simp, hfields.2.2.1, hfields.2.2.2⟩
  · simpa only [referenceEntryToolsFit, nextCache, hphase, historyUsed_append_write_report]
      using haligned.entry_tools
  · intro _ currentStage hcurrentCursor
    have heq : currentStage = stage := Fin.ext (hcurrentCursor.symm.trans hcursor)
    subst currentStage
    exact ⟨kind, current, hnextKind, hvalid, hnextRisk⟩
  · intro tool hcorrection
    rcases hcorrection with h | h <;> cases h


omit hlaminar in
private theorem replay_extend (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache nextCache : ReferenceReplayCache I)
    (event : VisibleEvent I)
    (hparse : tableReplay input initialAvailable budget history = some cache)
    (hstep : tableStep input initialAvailable budget cache event = some nextCache)
    (hfinal : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = history ++ [event]) :
    tableReplay input initialAvailable budget (history ++ [event]) = some nextCache := by
  have hs := tableReplay_some_spec input initialAvailable budget history cache hparse
  have hfold : (history ++ [event]).foldlM (tableStep input initialAvailable budget)
      (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  simp only [tableReplay, hs.1]
  rw [hfold]
  exact ite_eq_left hfinal

omit hlaminar in
private theorem historyCursor_append_noAdvance (history : List (VisibleEvent I))
    (event : VisibleEvent I) (hnone : eventAdvance event = none) :
    historyCursor (history ++ [event]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, hnone]

omit hlaminar in
private theorem historyUsed_append_noCommitment (history : List (VisibleEvent I))
    (event : VisibleEvent I) (hnone : eventCommitment event = none) :
    historyUsed (history ++ [event]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, hnone]

omit hlaminar in
private theorem replayCorrect_append_unrelated (cache : ReferenceReplayCache I)
    (event : VisibleEvent I) (phase : ReferenceReplayPhase I) (stage : I.Stage)
    (hw : eventWrite stage event = none) (hr : eventReport stage event = none) :
    referenceReplayCorrect {cache with seen := cache.seen ++ [event], phase := phase} stage =
      referenceReplayCorrect cache stage := by
  simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, hw, hr]

omit hlaminar in
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

omit hlaminar in
private theorem historyUsed_append_commitment (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool) :
    historyUsed (history ++ [.committed handle tool]) = insert tool (historyUsed history) := by
  simp [historyUsed, historyCommitments, List.filterMap_append, eventCommitment, Finset.union_comm]

/-- Allocation preservation uses an actual native Step and the original
entry-snapshot maximizer. It does not posit successful reference execution. -/
theorem tableStateAligned_allocate (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I)  (policy : PolicyRule I Unit)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable budget cache s)
    (hphase : cache.phase = .reported) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (handle : MismatchHandle I) (tool : I.Tool)
    (hmismatch : referenceReplayMismatch cache stage handle = true)
    (hpick : tableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) = some tool)
    (current : ℚ) (hcurrent : referenceReplayRisk budget cache = some current)
    (hstep : Step input C .uncapped accounting tapes s (.allocate handle tool) nextState) :
    ∃ nextCache, TableStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | allocate handle tool active valid compatible unused unallocated window resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.committed handle tool]
      phase := .allocated tool }
    have hs := tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans active
    have hstage := tableStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hhandleStage := referenceReplayMismatch_stage cache stage handle hmismatch
    have hpickSpec := (tableRepairTool_spec I hlaminar initialAvailable stage (historyUsed cache.entryHistory) tool hpick).1
    have hmem : tool ∈ initialAvailable := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpickSpec).2).1
    have hnotEntry : tool ∉ historyUsed cache.entryHistory := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpickSpec).2).2
    have hentry : historyUsed cache.entryHistory = historyUsed cache.seen := by
      simpa only [referenceEntryToolsFit, hphase] using haligned.entry_tools
    have hnot : tool ∉ historyUsed cache.seen := hentry ▸ hnotEntry
    have hcompat : tool ∈ I.eligible stage := hhandleStage ▸ compatible
    have hparser : tableStep input initialAvailable budget cache (.committed handle tool) = some nextCache := by
      simp [tableStep, hh, hstage, hcurrent, hphase, hmismatch, hcompat, hnot, hmem, hpick, nextCache]
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
      · simpa only [nextCache, tableKind, referenceReplayStage, hcur] using hk
      · have hcorrect := replayCorrect_append_unrelated cache (.committed handle tool) (.allocated tool) currentStage rfl rfl
        simpa only [nextCache, referenceReplayRisk, hcorrect] using hu
    · intro _ _
      exact ⟨current, hcurrent⟩

omit hlaminar in
theorem tableStateAligned_execute (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s nextState : State I} (initialAvailable : Finset I.Tool) (budget : ℚ)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input initialAvailable budget cache s)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) (handle : MismatchHandle I) (tool : I.Tool)
    (hphase : cache.phase = .allocated tool) (hmismatch : referenceReplayMismatch cache stage handle = true)
    (hstep : Step input C .uncapped accounting tapes s (.execute handle tool) nextState) :
    ∃ nextCache, TableStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.executed handle tool]
      phase := .executed tool }
    have hs := tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans active
    have hstage := tableStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hhandleStage := referenceReplayMismatch_stage cache stage handle hmismatch
    have hparser : tableStep input initialAvailable budget cache (.executed handle tool) = some nextCache := by
      simp [tableStep, hh, hstage, hphase, hmismatch, nextCache]
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
      · simpa only [nextCache, tableKind, referenceReplayStage, hcur] using hk
      · have hcorrect := replayCorrect_append_unrelated cache (.executed handle tool) (.executed tool) currentStage rfl rfl
        simpa only [nextCache, referenceReplayRisk, hcorrect] using hu
    · intro _ _
      exact haligned.correction_risk tool (Or.inl hphase)

omit hlaminar in
/-- Advancing opens the next stage only after its actual-prefix future port
has been shown clean. No correctness assumption is imposed on old outputs. -/
theorem tableStateAligned_advance (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I)  (policy : PolicyRule I Unit)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable budget cache s)
    (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hphase : (cache.phase = .reported ∧ referenceReplayCorrect cache stage = true) ∨
      ∃ tool, cache.phase = .executed tool)
    (current : ℚ) (hcurrent : referenceReplayRisk budget cache = some current)
    (hstep : Step input C .uncapped accounting tapes s (.advance stage) nextState) :
    ∃ nextCache, TableStateAligned input initialAvailable budget nextCache nextState := by
  cases hstep with
  | advance stage live written resources =>
    let nextCache : ReferenceReplayCache I := { cache with
      seen := cache.seen ++ [.advanced stage]
      entryHistory := cache.seen ++ [.advanced stage]
      phase := .testing }
    have hs := tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
    have hh : cache.halted = false := haligned.halted.trans live.1
    have hstage := tableStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
    have hcount : referencePhaseReportCount cache.phase = 1 := by
      rcases hphase with ⟨hphase, _⟩ | ⟨tool, hphase⟩ <;> simp [hphase, referencePhaseReportCount]
    have hparser : tableStep input initialAvailable budget cache (.advanced stage) = some nextCache := by
      simp [tableStep, hh, hstage, hcurrent, hphase, nextCache]
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

omit hlaminar in
theorem tableStateAligned_stop (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable budget cache s)
    (hactive : s.halted = false) (hphase : cache.phase = .testing) (hcursor : s.cursor = I.stageCount) :
    ∃ nextCache, TableStateAligned input initialAvailable budget nextCache (stopState s false) := by
  let nextCache : ReferenceReplayCache I := {cache with seen := cache.seen ++ [.stopped], halted := true}
  have hs := tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hc : historyCursor cache.seen = I.stageCount := haligned.cursor.trans hcursor
  have hparser : tableStep input initialAvailable budget cache .stopped = some nextCache := by
    simp [tableStep, hh, hc, hphase, nextCache]
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

omit hlaminar in
theorem prefix_replayMismatch_of_valid (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
     (policy : PolicyRule I Unit) (seed : Unit) (truth : I.Stage → Bool)
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

omit hlaminar in
theorem tableStateAligned_reported_mismatch (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) 
    (policy : PolicyRule I Unit) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input initialAvailable budget cache s)
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

omit hlaminar in
theorem tableStateAligned_reported_correct_risk (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : TableStateAligned input initialAvailable budget cache s)
    (hphase : cache.phase = .reported) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hcorrect : referenceReplayCorrect cache stage = true) :
    ∃ current, referenceReplayRisk budget cache = some current := by
  obtain ⟨kind, entryRisk, _, _, hu⟩ := haligned.reported_update
    (by simp [hphase, referencePhaseReportCount]) stage hcursor
  rw [hcorrect] at hu
  cases kind <;> simp only [referenceBudgetStep, Bool.not_true] at hu
  all_goals exact ⟨_, hu⟩

omit hlaminar in
theorem tableTestingAction_review_target (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : tableTestingAction input initialAvailable budget limit cache stage = .review stage) :
    (tableTarget I initialAvailable budget cache).isSome := by
  cases ht : tableTarget I initialAvailable budget cache with
  | some target => rfl
  | none =>
    cases hk : tableKind I initialAvailable cache with
    | none => simp [tableTestingAction, hk] at haction
    | some kind => cases kind <;> simp [tableTestingAction, hk, ht] at haction

/-- Preservation follows the actual seed/history rule at every real Step,
including truncation or abandonment. It is independent of eventual success. -/
theorem tableStateAligned_step  (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s nextState : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input initialAvailable budget limit) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input initialAvailable budget cache s)
    (hstep : Step input C .uncapped accounting tapes s
      (tableRule input initialAvailable budget limit seed s.history) nextState) :
    ∃ nextCache, TableStateAligned input initialAvailable budget nextCache nextState := by
  have hactive := step_source_active input C .uncapped accounting tapes hstep
  have habandon : tableRule input initialAvailable budget limit seed s.history = .abandon →
      ∃ nextCache, TableStateAligned input initialAvailable budget nextCache nextState := by
    intro ha
    have hs := hstep
    rw [ha] at hs
    have heq := step_deterministic input C .uncapped accounting tapes hs (.abandon s hactive)
    rw [heq]
    exact tableStateAligned_abandon input initialAvailable budget cache s haligned hactive
  by_cases hallow : historyAllowsAction s.history (tableCandidate input initialAvailable budget limit s.history)
  · have hrule : tableRule input initialAvailable budget limit seed s.history =
        tableCandidate input initialAvailable budget limit s.history := by
      exact ite_eq_left hallow
    have hh : cache.halted = false := haligned.halted.trans hactive
    by_cases hbound : s.cursor < I.stageCount
    · let stage : I.Stage := ⟨s.cursor, hbound⟩
      have hcursor : s.cursor = stage.val := rfl
      have hstage := tableStateAligned_stage input initialAvailable budget cache s haligned stage hcursor
      cases hphase : cache.phase with
      | written =>
        exact ((tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed).2.2.1 hphase).elim
      | testing =>
        have ha := tableRule_testing_eq_of_aligned input C accounting initialAvailable budget limit
          seed truth tapes hp hactive cache haligned hphase stage hcursor
        rcases tableTestingAction_supported input initialAvailable budget limit cache stage with hreview | ⟨bit, hwrite⟩ | habort
        · have hs := hstep
          rw [ha, hreview] at hs
          obtain ⟨nextCache, result, hs', ha'⟩ := tableStateAligned_review input C accounting tapes
            initialAvailable budget cache s haligned hphase hactive stage hcursor
            (tableTestingAction_review_target input initialAvailable budget limit cache stage hreview)
          rw [step_deterministic input C .uncapped accounting tapes hs hs']
          exact ⟨nextCache, ha'⟩
        · have hs := hstep
          rw [ha, hwrite] at hs
          obtain ⟨nextCache, result, hs', ha'⟩ := tableStateAligned_write hlaminar input C hearly accounting
            (tableRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget cache
            haligned hphase hactive stage hcursor bit
          rw [step_deterministic input C .uncapped accounting tapes hs hs']
          exact ⟨nextCache, ha'⟩
        · exact habandon (ha.trans habort)
      | reported =>
        cases hc : referenceReplayCorrect cache stage with
        | true =>
          have ha : tableRule input initialAvailable budget limit seed s.history = .advance stage := by
            rw [hrule]
            simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hc]
          have hs := hstep
          rw [ha] at hs
          obtain ⟨current, hcurrent⟩ := tableStateAligned_reported_correct_risk input initialAvailable budget cache s
            haligned hphase stage hcursor hc
          exact tableStateAligned_advance input C accounting (tableRule input initialAvailable budget limit)
            seed truth tapes hp initialAvailable budget cache haligned stage hcursor (Or.inl ⟨hphase, hc⟩) current hcurrent hs
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none =>
            apply habandon
            rw [hrule]
            simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hc, hr]
          | some current =>
            cases hv : referenceVisibleHandle s.history stage with
            | none =>
              apply habandon
              rw [hrule]
              simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hc, hr, hv]
            | some handle =>
              cases ht : tableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
              | none =>
                apply habandon
                rw [hrule]
                simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hc, hr, hv, ht]
              | some tool =>
                have ha : tableRule input initialAvailable budget limit seed s.history = .allocate handle tool := by
                  rw [hrule]
                  simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hc, hr, hv, ht]
                have hs := hstep
                rw [ha] at hs
                have hm := (tableStateAligned_reported_mismatch input C hearly accounting
                  (tableRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget cache
                  haligned hphase stage hcursor hc handle hv).2
                exact tableStateAligned_allocate hlaminar input C accounting (tableRule input initialAvailable budget limit)
                  seed truth tapes hp initialAvailable budget cache haligned hphase stage hcursor handle tool hm ht current hr hs
      | allocated tool =>
        cases hv : referenceVisibleHandle s.history stage with
        | none =>
          apply habandon
          rw [hrule]
          simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hv]
        | some handle =>
          have ha : tableRule input initialAvailable budget limit seed s.history = .execute handle tool := by
            rw [hrule]
            simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hv]
          have hs := hstep
          rw [ha] at hs
          obtain ⟨oldHandle, hhs, hvalid, _, _, _, _⟩ := by
            simpa only [hphase, referenceCurrentLedgerFits] using haligned.current_fields stage hcursor
          have hvo := prefix_visibleHandle_of_valid input C hearly .uncapped accounting
            (tableRule input initialAvailable budget limit) seed truth tapes hp oldHandle hvalid
          rw [hhs] at hvo
          have heq : handle = oldHandle := Option.some.inj (hv.symm.trans hvo)
          subst handle
          have hm := prefix_replayMismatch_of_valid input C hearly .uncapped accounting
            (tableRule input initialAvailable budget limit) seed truth tapes hp cache haligned.seen oldHandle hvalid
          rw [hhs] at hm
          exact tableStateAligned_execute input C accounting tapes initialAvailable budget cache haligned
            stage hcursor oldHandle tool hphase hm hs
      | executed tool =>
        have ha : tableRule input initialAvailable budget limit seed s.history = .advance stage := by
          rw [hrule]
          simp [tableCandidate, haligned.parsed, hh, hstage, hphase]
        have hs := hstep
        rw [ha] at hs
        obtain ⟨current, hcurrent⟩ := haligned.correction_risk tool (Or.inr hphase)
        exact tableStateAligned_advance input C accounting (tableRule input initialAvailable budget limit)
          seed truth tapes hp initialAvailable budget cache haligned stage hcursor (Or.inr ⟨tool, hphase⟩) current hcurrent hs
    · have hcursor : s.cursor = I.stageCount := by
        have hc := (prefix_cursorInvariant input C .uncapped accounting
          (tableRule input initialAvailable budget limit) seed truth tapes hp).bound
        omega
      have hs := tableReplay_some_spec input initialAvailable budget s.history cache haligned.parsed
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
      have ha : tableRule input initialAvailable budget limit seed s.history = .stop := by
        rw [hrule]
        simp [tableCandidate, haligned.parsed, hh, hstage, hhistory]
      have hs' := hstep
      rw [ha] at hs'
      rw [step_deterministic input C .uncapped accounting tapes hs' (.stop s hactive)]
      exact tableStateAligned_stop input initialAvailable budget cache s haligned hactive hphase hcursor
  · exact habandon (ite_eq_right hallow)

/-- Every actual finite Prefix of the unchanged controller has a replay
cache and ledger alignment, for arbitrary seed type and every truth/tape. -/
theorem prefix_tableStateAligned  (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input initialAvailable budget limit) seed truth tapes n s) :
    ∃ cache, TableStateAligned input initialAvailable budget cache s := by
  induction hp with
  | initial => exact ⟨referenceReplayInitial I, tableStateAligned_initial input initialAvailable budget hbudget hsmall truth⟩
  | next earlier step ih =>
    obtain ⟨cache, haligned⟩ := ih
    exact tableStateAligned_step hlaminar input C hearly accounting initialAvailable budget limit seed truth tapes earlier cache haligned step

omit hlaminar in
private theorem cursor_of_replayStage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage with hb
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

/-- The finite permission guard is nonbinding at any genuinely aligned
Prefix. This is proved from observable queries and actual ledger invariants,
not supplied as a condition on the controller. -/
theorem tableCandidate_allowed_of_aligned 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (policy : PolicyRule I Unit) (seed : Unit)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input initialAvailable budget cache s) :
    historyAllowsAction s.history (tableCandidate input initialAvailable budget limit s.history) := by
  cases hh : cache.halted with
  | true => simp [tableCandidate, haligned.parsed, hh, historyAllowsAction]
  | false =>
    cases hs : referenceReplayStage I cache with
    | none =>
      simp only [tableCandidate, haligned.parsed, hh, Bool.false_eq_true, ite_false, hs]
      split_ifs <;> trivial
    | some stage =>
      have hcursor : s.cursor = stage.val := haligned.cursor.symm.trans (cursor_of_replayStage cache stage hs)
      have hch : historyCursor s.history = stage.val := by rw [← haligned.seen]; exact haligned.cursor.trans hcursor
      cases hphase : cache.phase with
      | testing =>
        have hcand : tableCandidate input initialAvailable budget limit s.history =
            tableTestingAction input initialAvailable budget limit cache stage := by
          simp [tableCandidate, haligned.parsed, hh, hs, hphase]
        rw [hcand]
        exact tableTestingAction_allowed_of_aligned input C accounting policy seed truth tapes hp
          initialAvailable budget limit cache haligned hphase stage hcursor
      | written => simp [tableCandidate, haligned.parsed, hh, hs, hphase, historyAllowsAction]
      | reported =>
        have hf := haligned.current_fields stage hcursor
        simp only [hphase, referenceCurrentLedgerFits] at hf
        cases hc : referenceReplayCorrect cache stage with
        | true =>
          have hcand : tableCandidate input initialAvailable budget limit s.history = .advance stage := by
            simp [tableCandidate, haligned.parsed, hh, hs, hphase, hc]
          rw [hcand]
          refine ⟨hch, ?_⟩
          rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
          exact hf.1
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none => simp [tableCandidate, haligned.parsed, hh, hs, hphase, hc, hr, historyAllowsAction]
          | some current =>
            cases hv : referenceVisibleHandle s.history stage with
            | none => simp [tableCandidate, haligned.parsed, hh, hs, hphase, hc, hr, hv, historyAllowsAction]
            | some handle =>
              cases ht : tableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
              | none => simp [tableCandidate, haligned.parsed, hh, hs, hphase, hc, hr, hv, ht, historyAllowsAction]
              | some tool =>
                have hcand : tableCandidate input initialAvailable budget limit s.history = .allocate handle tool := by
                  simp [tableCandidate, haligned.parsed, hh, hs, hphase, hc, hr, hv, ht]
                rw [hcand]
                obtain ⟨hvalid, hm⟩ := tableStateAligned_reported_mismatch input C hearly accounting policy seed truth tapes hp
                  initialAvailable budget cache haligned hphase stage hcursor hc handle hv
                have hhs := referenceReplayMismatch_stage cache stage handle hm
                have hpick := (tableRepairTool_spec I hlaminar initialAvailable stage (historyUsed cache.entryHistory) tool ht).1
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
        | none => simp [tableCandidate, haligned.parsed, hh, hs, hphase, hv, historyAllowsAction]
        | some handle =>
          have hcand : tableCandidate input initialAvailable budget limit s.history = .execute handle tool := by
            simp [tableCandidate, haligned.parsed, hh, hs, hphase, hv]
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
        have hcand : tableCandidate input initialAvailable budget limit s.history = .advance stage := by
          simp [tableCandidate, haligned.parsed, hh, hs, hphase]
        rw [hcand]
        refine ⟨hch, ?_⟩
        rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
        have hf := haligned.current_fields stage hcursor
        simp only [hphase, referenceCurrentLedgerFits] at hf
        exact hf.1

/-- Every actual controller Prefix runs its original candidate action;
the visible permission check does not add an abandonment branch. -/
theorem tableRule_eq_candidate_of_prefix 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input initialAvailable budget limit) seed truth tapes n s) :
    tableRule input initialAvailable budget limit seed s.history =
      tableCandidate input initialAvailable budget limit s.history := by
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting initialAvailable budget hbudget hsmall
    limit seed truth tapes hp
  exact ite_eq_left (tableCandidate_allowed_of_aligned hlaminar input C hearly accounting
    (tableRule input initialAvailable budget limit) seed truth tapes hp initialAvailable budget limit cache haligned)


end PaperProofs.Common.Native.PSTRStatistics.TableAlignment
