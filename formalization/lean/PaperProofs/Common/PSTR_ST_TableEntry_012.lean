module

public import PaperProofs.Common.PSTR_ST_TableTermination_011

/-! Real table stage-entry budget trace. Entry records, original three-case
budget labels and actual advances are derived from the genuine table Prefix,
not supplied as performance hypotheses or generic/table path equalities. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableEntry

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice TableAlignment TableOrigin TableDecision TableInfinite TableTermination

variable {I : Instance} (hlaminar : LaminarSchedule I.compatibility)
include hlaminar

omit hlaminar in
private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

omit hlaminar in
private def StepShape (cache next : ReferenceReplayCache I) (event : VisibleEvent I) : Prop :=
  match event with
  | .observation stage symbol => cache.phase = .testing ∧
      next = {cache with seen := cache.seen ++ [.observation stage symbol]}
  | .wrote _ _ _ => cache.phase = .testing
  | .report _ _ _ => next.phase = .reported
  | .committed handle tool => cache.phase = .reported ∧
      next = {cache with seen := cache.seen ++ [.committed handle tool], phase := .allocated tool}
  | .executed handle tool => cache.phase = .allocated tool ∧
      next = {cache with seen := cache.seen ++ [.executed handle tool], phase := .executed tool}
  | .advanced stage => next = {cache with
      seen := cache.seen ++ [.advanced stage]
      entryHistory := cache.seen ++ [.advanced stage]
      phase := .testing}
  | .stopped | .abandoned => next.halted = true

omit hlaminar in
private theorem replay_step_shape (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hstep : tableStep input available budget cache event = some next) : StepShape cache next event := by
  cases hh : cache.halted with
  | true => simp only [tableStep, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      exact ⟨hg.2.2.1, by simpa only [hh] using he⟩
    | wrote stage bit serial =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      exact (some_if_some _ _ _ hstep).1.2.2
    | report stage truth serial =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      rw [(some_if_some _ _ _ hstep).2]
      rfl
    | committed handle tool =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      exact ⟨hg.1, by simpa only [hh] using he⟩
    | executed handle tool =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      exact ⟨hg.1, by simpa only [hh] using he⟩
    | advanced stage =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      simpa only [StepShape, hh] using (some_if_some _ _ _ hstep).2
    | stopped | abandoned =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      rw [(some_if_some _ _ _ hstep).2]
      rfl

omit hlaminar in
private theorem replay_packet_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history packet : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hparse : tableReplay input available budget history = some cache)
    (hnext : tableReplay input available budget (history ++ packet) = some next) :
    packet.foldlM (tableStep input available budget) cache = some next := by
  have hs := tableReplay_some_spec input available budget history cache hparse
  have hs' := tableReplay_some_spec input available budget (history ++ packet) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

omit hlaminar in
private theorem replay_single_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : tableReplay input available budget history = some cache)
    (hnext : tableReplay input available budget (history ++ [event]) = some next) :
    tableStep input available budget cache event = some next := by
  simpa using replay_packet_after input available budget history [event] cache next hparse hnext

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
private theorem prefix_eq_run_sample  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [hw] using he

omit hlaminar in
private theorem entry_at_increment  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Unit × input.World)
    (n : ℕ) (old next : State I) (stage : I.Stage)
    (hold : run input C .uncapped accounting rule sample n = old)
    (hnext : run input C .uncapped accounting rule sample (n + 1) = next)
    (hbefore : old.cursor < stage.val) (hcursor : next.cursor = stage.val) :
    entryHistory input C .uncapped accounting rule stage sample = some next.history := by
  apply (entryHistory_some_iff input C .uncapped accounting rule stage sample next.history).mpr
  refine ⟨n + 1, by simpa only [hnext] using hcursor, ?_, by rw [hnext]⟩
  intro k hk he
  have hm := run_cursor_monotone input C .uncapped accounting rule hlegal sample (Nat.le_of_lt_succ hk)
  dsimp only at hm
  rw [hold, he] at hm
  omega

omit hlaminar in
/-- A theorem-level witness of the real stage-entry cache and its budget.
It is derived from Prefix, and is never an executable cache/Policy field. -/
structure TableEntryBudgetTrace  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World) (cache entry_cache : ReferenceReplayCache I) (stage : I.Stage) : Prop where
  actual_entry : entryHistory input C .uncapped accounting (tableRule input available budget none)
    stage sample = some cache.entryHistory
  parsed_entry : tableReplay input available budget cache.entryHistory = some entry_cache
  entry_testing : entry_cache.phase = .testing
  entry_active : entry_cache.halted = false
  entry_seen : entry_cache.seen = cache.entryHistory
  entry_snapshot : entry_cache.entryHistory = cache.entryHistory
  entry_cursor : historyCursor entry_cache.seen = stage.val
  testing_events : cache.phase = .testing → cache.events = entry_cache.events
  reported_budget : referencePhaseReportCount cache.phase = 1 →
    ∃ kind risk, tableKind I available entry_cache = some kind ∧
      ReferenceBudgetValid risk ∧ referenceReplayRisk budget entry_cache = some risk ∧
      referenceReplayRisk budget cache = referenceBudgetStep kind (!(referenceReplayCorrect cache stage)) risk

omit hlaminar in
private theorem kind_at_entry (available : Finset I.Tool) (cache entry : ReferenceReplayCache I)
    (hcursor : historyCursor cache.seen = historyCursor entry.seen)
    (hsnapshot : cache.entryHistory = entry.entryHistory) :
    tableKind I available cache = tableKind I available entry := by
  simp only [tableKind, referenceReplayStage, hcursor, hsnapshot]

/-- The real first-entry snapshot and its original budget survive every
phase of the same actual reference prefix, for an arbitrary seed universe. -/
theorem prefix_tableEntryBudgetTrace 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ cache : ReferenceReplayCache I, TableStateAligned input available budget cache s →
      s.halted = false → ∀ stage : I.Stage, s.cursor = stage.val →
      ∃ entry, TableEntryBudgetTrace input C accounting available budget sample cache entry stage := by
  induction hp with
  | initial =>
    intro cache haligned _ stage hcursor
    have hi := tableReplay_initial input available budget hbudget hsmall
    have he : cache = referenceReplayInitial I := Option.some.inj (haligned.parsed.symm.trans hi)
    subst cache
    refine ⟨referenceReplayInitial I, ?_⟩
    constructor
    · exact entryHistory_stageZero input C .uncapped accounting (tableRule input available budget none)
        stage hcursor.symm sample
    · exact hi
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hcursor
    · intro _; rfl
    · intro h
      simp only [referenceReplayInitial, referencePhaseReportCount] at h
      contradiction
  | @next n s next earlier step ih =>
    intro cache haligned hactive stage hcursor
    obtain ⟨old, hold⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier
    generalize haction : tableRule input available budget none sample.1 s.history = action at step
    cases step with
    | review current live port resources =>
      change s.cursor = stage.val at hcursor
      have heq : current = stage := Fin.ext (live.2.symm.trans hcursor)
      subst current
      have hsingle := replay_single_after input available budget s.history old cache
        (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
        hold.parsed haligned.parsed
      obtain ⟨hphase, he⟩ := replay_step_shape input available budget old cache _ hsingle
      subst cache
      obtain ⟨entry, horigin⟩ := ih old hold live.1 stage live.2
      refine ⟨entry, horigin.actual_entry, horigin.parsed_entry, horigin.entry_testing, horigin.entry_active,
        horigin.entry_seen, horigin.entry_snapshot, horigin.entry_cursor, ?_, ?_⟩
      · intro _
        exact horigin.testing_events hphase
      · intro h
        simp only [hphase, referencePhaseReportCount] at h
        contradiction
    | allocate handle tool active valid compatible unused unallocated window resources =>
      change s.cursor = stage.val at hcursor
      have hsingle := replay_single_after input available budget s.history old cache (.committed handle tool)
        hold.parsed haligned.parsed
      obtain ⟨hphase, he⟩ := replay_step_shape input available budget old cache _ hsingle
      subst cache
      obtain ⟨entry, horigin⟩ := ih old hold active stage hcursor
      refine ⟨entry, horigin.actual_entry, horigin.parsed_entry, horigin.entry_testing, horigin.entry_active,
        horigin.entry_seen, horigin.entry_snapshot, horigin.entry_cursor, ?_, ?_⟩
      · intro h; cases h
      · intro _
        obtain ⟨kind, risk, hk, hv, hr, hu⟩ := horigin.reported_budget (by simp [hphase, referencePhaseReportCount])
        refine ⟨kind, risk, hk, hv, hr, ?_⟩
        have hc : referenceReplayCorrect {old with
            seen := old.seen ++ [.committed handle tool]
            phase := .allocated tool} stage = referenceReplayCorrect old stage := by
          simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, eventWrite, eventReport]
        simpa only [referenceReplayRisk, hc] using hu
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      change s.cursor = stage.val at hcursor
      have hsingle := replay_single_after input available budget s.history old cache (.executed handle tool)
        hold.parsed haligned.parsed
      obtain ⟨hphase, he⟩ := replay_step_shape input available budget old cache _ hsingle
      subst cache
      obtain ⟨entry, horigin⟩ := ih old hold active stage hcursor
      refine ⟨entry, horigin.actual_entry, horigin.parsed_entry, horigin.entry_testing, horigin.entry_active,
        horigin.entry_seen, horigin.entry_snapshot, horigin.entry_cursor, ?_, ?_⟩
      · intro h; cases h
      · intro _
        obtain ⟨kind, risk, hk, hv, hr, hu⟩ := horigin.reported_budget (by simp [hphase, referencePhaseReportCount])
        refine ⟨kind, risk, hk, hv, hr, ?_⟩
        have hc : referenceReplayCorrect {old with
            seen := old.seen ++ [.executed handle tool]
            phase := .executed tool} stage = referenceReplayCorrect old stage := by
          simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, eventWrite, eventReport]
        simpa only [referenceReplayRisk, hc] using hu
    | write current bit live port resources =>
      change s.cursor = stage.val at hcursor
      have heq : current = stage := Fin.ext (live.2.symm.trans hcursor)
      subst current
      have hpacket := replay_packet_after input available budget s.history (writeResponses C s stage bit) old cache
        hold.parsed haligned.parsed
      have hpacket' : [VisibleEvent.wrote stage bit s.clock, VisibleEvent.report stage (s.ledger.truth stage) s.clock].foldlM
          (tableStep input available budget) old = some cache := by
        simpa only [writeResponses, hearly, ite_true, writeLedger, List.singleton_append] using hpacket
      cases hw : tableStep input available budget old (.wrote stage bit s.clock) with
      | none => simp [hw] at hpacket'
      | some written =>
        have hphase : old.phase = .testing := replay_step_shape input available budget old written _ hw
        obtain ⟨entry, horigin⟩ := ih old hold live.1 stage live.2
        obtain ⟨kind, risk, hk, hr, hv, hlen⟩ := tableStateAligned_testing_ready hlaminar input available budget old s hold hphase stage live.2
        have hh : old.halted = false := hold.halted.trans live.1
        have hstage := tableStateAligned_stage input available budget old s hold stage live.2
        have hserial : s.clock = (historyActions old.seen).length := by
          rw [hold.seen]
          exact (prefix_historyActions_length input C .uncapped accounting (tableRule input available budget none)
            sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier).symm
        have hcanonical := tableReplay_write_packet input available budget s.history old hold.parsed hh hphase
          stage hstage kind hk risk hr hlen bit (s.ledger.truth stage) s.clock hserial
        have he : cache = {old with
            seen := old.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
            events := old.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
            phase := .reported} := by
          apply Option.some.inj
          exact haligned.parsed.symm.trans (by
            simpa only [record, writeResponses, hearly, ite_true, writeLedger, List.singleton_append] using hcanonical)
        subst cache
        have hevents := horigin.testing_events hphase
        have hentryRisk : referenceReplayRisk budget entry = some risk := by
          simpa only [referenceReplayRisk, hevents] using hr
        have hentryKind : tableKind I available entry = some kind := by
          have hc : historyCursor old.seen = historyCursor entry.seen :=
            (hold.cursor.trans live.2).trans horigin.entry_cursor.symm
          rw [← kind_at_entry available old entry hc horigin.entry_snapshot.symm]
          exact hk
        refine ⟨entry, horigin.actual_entry, horigin.parsed_entry, horigin.entry_testing, horigin.entry_active,
          horigin.entry_seen, horigin.entry_snapshot, horigin.entry_cursor, ?_, ?_⟩
        · intro h; cases h
        · intro _
          refine ⟨kind, risk, hentryKind, hv, hentryRisk, ?_⟩
          have hc : referenceReplayCorrect {old with
              seen := old.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
              events := old.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
              phase := .reported} stage = decide (bit = s.ledger.truth stage) := by
            simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons, eventWrite, eventReport]
          rw [hc]
          simp only [referenceReplayRisk, budgetPath_append, referenceBudgetPath]
          change (referenceReplayRisk budget old).bind
            (fun child => (referenceBudgetStep kind (decide (bit ≠ s.ledger.truth stage)) child).bind some) = _
          rw [hr]
          simp
    | advance current live written resources =>
      have hsingle := replay_single_after input available budget s.history old cache (.advanced current)
        hold.parsed haligned.parsed
      have he := replay_step_shape input available budget old cache _ hsingle
      change cache = {old with
        seen := old.seen ++ [.advanced current]
        entryHistory := old.seen ++ [.advanced current]
        phase := .testing} at he
      subst cache
      have hbefore : s.cursor < stage.val := by
        change s.cursor + 1 = stage.val at hcursor
        omega
      have hpnext : Prefix input C .uncapped accounting (tableRule input available budget none)
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) (n + 1)
          (record accounting s (.advance current) [.advanced current] (advanceLedger s current) (s.cursor + 1) false) := by
        apply Prefix.next earlier
        rw [haction]
        exact .advance s current live written resources
      have hentry := entry_at_increment input C accounting (tableRule input available budget none)
        (tableRule_uncapped_legal input C hearly accounting available budget none) sample n s _ stage
        (prefix_eq_run_sample input C accounting (tableRule input available budget none) sample earlier)
        (prefix_eq_run_sample input C accounting (tableRule input available budget none) sample hpnext) hbefore hcursor
      refine ⟨{old with
        seen := old.seen ++ [.advanced current]
        entryHistory := old.seen ++ [.advanced current]
        phase := .testing}, ?_⟩
      constructor
      · simpa only [hold.seen, record] using hentry
      · simpa only [hold.seen, record] using haligned.parsed
      · rfl
      · exact hold.halted.trans live.1
      · rfl
      · rfl
      · exact haligned.cursor.trans hcursor
      · intro _; rfl
      · intro h
        simp only [referencePhaseReportCount] at h
        contradiction
    | stop | abandon => cases hactive

omit hlaminar in
/-- The original rational continuation budget reconstructed from one actual
entry history; malformed histories give none. No truth/world is an argument. -/
def tableEntryRisk (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : Option ℚ := do
  let cache ← tableReplay input available budget history
  referenceReplayRisk budget cache

omit hlaminar in
def tableEntryKind (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : Option ReferenceBudgetCase := do
  let cache ← tableReplay input available budget history
  tableKind I available cache

omit hlaminar in
theorem measurable_tableEntryRisk (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) : Measurable (tableEntryRisk input available budget) := measurable_of_countable _

omit hlaminar in
theorem tableEntryRisk_initial (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    tableEntryRisk input available budget [] = some (budget / 2) := by
  simp only [tableEntryRisk, tableReplay_initial input available budget hbudget hsmall,
    Option.bind_eq_bind, Option.bind_some]
  rfl

/-- The trace is derived without an alignment premise on the policy: the
canonical cache and the true entry witness both come from actual Prefix. -/
theorem tableEntryBudgetTrace_of_prefix 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    ∃ cache entry, TableStateAligned input available budget cache s ∧
      TableEntryBudgetTrace input C accounting available budget sample cache entry stage := by
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  obtain ⟨entry, horigin⟩ := prefix_tableEntryBudgetTrace hlaminar input C hearly accounting available budget
    hbudget hsmall sample hp cache haligned hactive stage hcursor
  exact ⟨cache, entry, haligned, horigin⟩

omit hlaminar in
/-- At any actual reported/repair phase, the risk used by reported_update
is exactly the budget parsed at the real first entry, not an unbound witness. -/
theorem TableEntryBudgetTrace.reported_risk 
    {input : StatisticalInput I} {C : Contract I} {accounting : NormalAccounting I}
    {available : Finset I.Tool} {budget : ℚ} {sample : Unit × input.World}
    {cache entry : ReferenceReplayCache I} {stage : I.Stage}
    (horigin : TableEntryBudgetTrace input C accounting available budget sample cache entry stage)
    (hphase : referencePhaseReportCount cache.phase = 1) :
    ∃ kind risk,
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some cache.entryHistory ∧
      tableEntryKind input available budget cache.entryHistory = some kind ∧
      tableEntryRisk input available budget cache.entryHistory = some risk ∧
      ReferenceBudgetValid risk ∧
      referenceReplayRisk budget cache = referenceBudgetStep kind (!(referenceReplayCorrect cache stage)) risk := by
  obtain ⟨kind, risk, hk, hv, hr, hu⟩ := horigin.reported_budget hphase
  refine ⟨kind, risk, horigin.actual_entry, ?_, ?_, hv, hu⟩
  · simp only [tableEntryKind, horigin.parsed_entry, Option.bind_eq_bind, Option.bind_some, hk]
  · simp only [tableEntryRisk, horigin.parsed_entry, Option.bind_eq_bind, Option.bind_some, hr]

/-- An actual advance transfers exactly the original updated budget to the
next genuine entry. All rank/tool selection remains before current commit;
the error bit is the current real ordinary report, not a hypothetical branch. -/
theorem tableAdvance_entry_budget 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (stage nextStage : I.Stage) (hnextStage : nextStage.val = stage.val + 1)
    (hstep : Step input C .uncapped accounting (worldTapes input sample.2) s (.advance stage) next)
    (haction : tableRule input available budget none sample.1 s.history = .advance stage) :
    ∃ cache history kind risk,
      TableStateAligned input available budget cache s ∧
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
      entryHistory input C .uncapped accounting (tableRule input available budget none) nextStage sample = some next.history ∧
      tableEntryKind input available budget history = some kind ∧
      tableEntryRisk input available budget history = some risk ∧ ReferenceBudgetValid risk ∧
      tableEntryRisk input available budget next.history =
        referenceBudgetStep kind (!(referenceReplayCorrect cache stage)) risk := by
  have hactive := step_source_active input C .uncapped accounting (worldTapes input sample.2) hstep
  have hpnext : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) (n + 1) next := by
    apply Prefix.next hp
    rw [haction]
    exact hstep
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  obtain ⟨nextCache, hnextAligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext
  cases hstep with
  | advance stage live written resources =>
    have hsingle := replay_single_after input available budget s.history cache nextCache (.advanced stage)
      haligned.parsed hnextAligned.parsed
    have he := replay_step_shape input available budget cache nextCache _ hsingle
    have hh : cache.halted = false := haligned.halted.trans live.1
    simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hsingle
    obtain ⟨_, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
    obtain ⟨_, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
    have hphase : referencePhaseReportCount cache.phase = 1 := by
      rcases (some_if_some _ _ _ hsingle).1.2 with ⟨hphase, _⟩ | ⟨tool, hphase⟩ <;>
        simp [hphase, referencePhaseReportCount]
    obtain ⟨entry, horigin⟩ := prefix_tableEntryBudgetTrace hlaminar input C hearly accounting available budget hbudget hsmall
      sample hp cache haligned live.1 stage live.2
    obtain ⟨kind, risk, hentry, hk, hr, hv, hu⟩ := horigin.reported_risk hphase
    have hcursorNext : (record accounting s (.advance stage) [.advanced stage]
        (advanceLedger s stage) (s.cursor + 1) false).cursor = nextStage.val := by
      change s.cursor + 1 = nextStage.val
      rw [live.2, hnextStage]
    have hbefore : s.cursor < nextStage.val := by rw [live.2, hnextStage]; omega
    have hentryNext := entry_at_increment input C accounting (tableRule input available budget none)
      (tableRule_uncapped_legal input C hearly accounting available budget none) sample n s _ nextStage
      (prefix_eq_run_sample input C accounting (tableRule input available budget none) sample hp)
      (prefix_eq_run_sample input C accounting (tableRule input available budget none) sample hpnext) hbefore hcursorNext
    refine ⟨cache, cache.entryHistory, kind, risk, haligned, hentry, hentryNext, hk, hr, hv, ?_⟩
    simp only [tableEntryRisk, hnextAligned.parsed, Option.bind_eq_bind, Option.bind_some]
    rw [he]
    exact hu

omit hlaminar in
private theorem run_first_stage_active 
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Unit) (hlegal : LegalRule input C .uncapped accounting rule)
    (sample : Unit × input.World) (stage : I.Stage) (n : ℕ)
    (hcursor : (run input C .uncapped accounting rule sample n).cursor = stage.val)
    (hbefore : ∀ k < n, (run input C .uncapped accounting rule sample k).cursor ≠ stage.val) :
    (run input C .uncapped accounting rule sample n).halted = false := by
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hh : (run input C .uncapped accounting rule sample n).halted = true
    · rw [run_succ_of_halted input C .uncapped accounting rule sample n hh] at hcursor
      exact (hbefore n (Nat.lt_succ_self n) hcursor).elim
    · have ha : (run input C .uncapped accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
      have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample n ha
      obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ hp ha
      have he := run_succ_of_step input C .uncapped accounting rule sample n next ha hs
      rw [he] at hcursor ⊢
      generalize haction : rule sample.1 (run input C .uncapped accounting rule sample n).history = action at hs
      cases hs with
      | review | write | allocate | execute | advance => rfl
      | stop | abandon =>
        exact (hbefore n (Nat.lt_succ_self n) hcursor).elim

/-- Every genuine Some entry has a valid original rational budget and rank
case, reconstructed solely from that finite entry history. Its target is
exactly the original three-branch target, including None for infinite rank. -/
theorem tableEntryRisk_kind_target 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (tableRule input available budget none)
      stage sample = some history) :
    ∃ kind risk,
      tableEntryKind input available budget history = some kind ∧
      tableEntryRisk input available budget history = some risk ∧ ReferenceBudgetValid risk ∧
      tableEntryTarget input available budget history = referenceBudgetTarget kind risk := by
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (tableRule input available budget none) stage sample history).mp hentry
  have hlegal : LegalRule input C .uncapped accounting (tableRule  input available budget none) :=
    tableRule_uncapped_legal input C hearly accounting available budget none
  have ha := run_first_stage_active input C accounting (tableRule input available budget none) hlegal sample stage n hcursor hbefore
  have hp := run_prefix_of_active input C .uncapped accounting (tableRule input available budget none) hlegal sample n ha
  obtain ⟨cache, entry, haligned, horigin⟩ := tableEntryBudgetTrace_of_prefix hlaminar input C hearly accounting available budget
    hbudget hsmall sample hp ha stage hcursor
  have hsnapshot : cache.entryHistory = history := Option.some.inj (horigin.actual_entry.symm.trans hentry)
  have hparse : tableReplay input available budget history = some cache := by
    rw [← hhistory]
    exact haligned.parsed
  have hparseEntry : tableReplay input available budget history = some entry := by
    rw [← hsnapshot]
    exact horigin.parsed_entry
  have heq : entry = cache := Option.some.inj (hparseEntry.symm.trans hparse)
  subst entry
  obtain ⟨kind, risk, hk, hr, hv, hlen⟩ := tableStateAligned_testing_ready hlaminar input available budget cache _ haligned
    horigin.entry_testing stage hcursor
  refine ⟨kind, risk, ?_, ?_, hv, ?_⟩
  · simp only [tableEntryKind, hparse, Option.bind_eq_bind, Option.bind_some, hk]
  · simp only [tableEntryRisk, hparse, Option.bind_eq_bind, Option.bind_some, hr]
  · simp only [tableEntryTarget, hparse, Option.bind_eq_bind, Option.bind_some]
    cases kind <;>
      simp [tableTarget, horigin.entry_active, horigin.entry_testing, hk, hr,
        hv.1, Nat.le_of_lt hlen, referenceBudgetTarget]
    all_goals simpa only [one_div] using hv.2

omit hlaminar in
/-- Conversely, every actual next-stage entry is produced by an actual
advance of its predecessor, before that next stage has taken any action.
This supplies the event-source direction needed for entry-mass transport. -/
theorem tableNextEntry_has_advance 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (tableRule input available budget none)
      nextStage sample = some history) :
    ∃ (n : ℕ) (s next : State I),
      Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n s ∧
      run input C .uncapped accounting (tableRule input available budget none) sample n = s ∧
      Step input C .uncapped accounting (worldTapes input sample.2) s (.advance stage) next ∧
      tableRule input available budget none sample.1 s.history = .advance stage ∧ next.history = history := by
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (tableRule input available budget none) nextStage sample history).mp hentry
  cases n with
  | zero =>
    change 0 = nextStage.val at hcursor
    have hs := stage.isLt
    omega
  | succ n =>
    have hlegal : LegalRule input C .uncapped accounting (tableRule  input available budget none) :=
      tableRule_uncapped_legal input C hearly accounting available budget none
    have ha : (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      rw [run_succ_of_halted input C .uncapped accounting (tableRule input available budget none) sample n hh] at hcursor
      exact hbefore n (Nat.lt_succ_self n) hcursor
    have hp := run_prefix_of_active input C .uncapped accounting (tableRule input available budget none) hlegal sample n ha
    obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ hp ha
    have he := run_succ_of_step input C .uncapped accounting (tableRule input available budget none) sample n next ha hs
    rw [he] at hcursor hhistory
    generalize haction : tableRule input available budget none sample.1
      (run input C .uncapped accounting (tableRule input available budget none) sample n).history = action at hs
    cases hs with
    | review | write | allocate | execute | stop | abandon =>
      exact (hbefore n (Nat.lt_succ_self n) hcursor).elim
    | advance current live written resources =>
      have hcurrent : current = stage := by
        apply Fin.ext
        change (run input C .uncapped accounting (tableRule input available budget none) sample n).cursor + 1 = nextStage.val at hcursor
        have hc := live.2
        omega
      subst current
      exact ⟨n, _, _, hp, rfl, .advance _ stage live written resources, haction, hhistory⟩


end PaperProofs.Common.Native.PSTRStatistics.TableEntry
