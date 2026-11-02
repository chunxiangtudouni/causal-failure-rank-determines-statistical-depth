module

public import PaperProofs.Common.ReferenceSuffixReplay
public import PaperProofs.Common.HistorySuffixWorld

/-!
Continuation of the unchanged reference on a genuine visible entry prefix.
Cache joining uses only old visible history and its public budget labels.
The proof-only base facts below are derived from real entries; they are not
Policy fields or additional alignment/Markov/performance assumptions.
The full actual run and remaining observation-bill identities below cover
all returned-action clocks, failed/abandoned paths and infinite charges.
The asymptotic reference-cost upper bound is a separate obligation.
-/

@[expose] public section

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {I : Instance}

def referenceSuffixPhaseLift (I : Instance) (first : ℕ) :
    ReferenceReplayPhase (I.freshSuffix first) → ReferenceReplayPhase I
  | .testing => .testing
  | .written => .written
  | .reported => .reported
  | .allocated tool => .allocated tool
  | .executed tool => .executed tool

theorem referenceSuffixPhaseLift_testing (I : Instance) (first : ℕ)
    (phase : ReferenceReplayPhase (I.freshSuffix first)) :
    referenceSuffixPhaseLift I first phase = .testing ↔ phase = .testing := by cases phase <;> simp [referenceSuffixPhaseLift]

theorem referenceSuffixPhaseLift_written (I : Instance) (first : ℕ)
    (phase : ReferenceReplayPhase (I.freshSuffix first)) :
    referenceSuffixPhaseLift I first phase = .written ↔ phase = .written := by cases phase <;> simp [referenceSuffixPhaseLift]

theorem referenceSuffixPhaseLift_reported (I : Instance) (first : ℕ)
    (phase : ReferenceReplayPhase (I.freshSuffix first)) :
    referenceSuffixPhaseLift I first phase = .reported ↔ phase = .reported := by cases phase <;> simp [referenceSuffixPhaseLift]

theorem referenceSuffixPhaseLift_allocated (I : Instance) (first : ℕ)
    (phase : ReferenceReplayPhase (I.freshSuffix first)) (tool : I.Tool) :
    referenceSuffixPhaseLift I first phase = .allocated tool ↔ phase = .allocated tool := by
  cases phase <;> simp [referenceSuffixPhaseLift]
  exact ⟨fun h => congrArg (ReferenceReplayPhase.allocated (I := I.freshSuffix first))
      (ReferenceReplayPhase.allocated.inj (I := I) h),
    fun h => congrArg (ReferenceReplayPhase.allocated (I := I))
      (ReferenceReplayPhase.allocated.inj (I := I.freshSuffix first) h)⟩

def referenceSuffixHistoryJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) : List (VisibleEvent I) :=
  before ++ referenceSuffixHistoryLift I first (historyActions before).length after

theorem referenceSuffixHistoryJoin_append (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after rest : List (VisibleEvent (I.freshSuffix first))) :
    referenceSuffixHistoryJoin I first before (after ++ rest) =
      referenceSuffixHistoryJoin I first before after ++
        referenceSuffixHistoryLift I first (historyActions before).length rest := by
  simp only [referenceSuffixHistoryJoin, referenceSuffixHistoryLift_append, List.append_assoc]

theorem historyCursor_referenceSuffixJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    historyCursor (referenceSuffixHistoryJoin I first before after) = historyCursor before + historyCursor after := by
  calc
    _ = historyCursor before + historyCursor (referenceSuffixHistoryLift I first (historyActions before).length after) := by
      simp only [referenceSuffixHistoryJoin, historyCursor, List.filterMap_append, List.length_append]
    _ = _ := congrArg (historyCursor before + ·) (historyCursor_referenceSuffixLift I first _ after)

theorem historyActions_referenceSuffixJoin_length (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    (historyActions (referenceSuffixHistoryJoin I first before after)).length =
      (historyActions before).length + (historyActions after).length := by
  calc
    _ = (historyActions before).length + (historyActions (referenceSuffixHistoryLift I first (historyActions before).length after)).length := by
      simp only [referenceSuffixHistoryJoin, historyActions, List.filterMap_append, List.length_append]
    _ = _ := congrArg ((historyActions before).length + ·) (historyActions_referenceSuffixLift_length I first _ after)

theorem historyUsed_referenceSuffixJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    historyUsed (referenceSuffixHistoryJoin I first before after) = historyUsed before ∪ historyUsed (I := I.freshSuffix first) after := by
  classical
  have ha : ∀ (left right : List (VisibleEvent I)), historyUsed (left ++ right) = historyUsed left ∪ historyUsed right := by
    intro left right
    simp only [historyUsed, historyCommitments, List.filterMap_append, List.map_append, List.toFinset_append]
  rw [referenceSuffixHistoryJoin, ha, historyUsed_referenceSuffixLift]

theorem historyObservations_referenceSuffixJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage)
    (hbefore : historyObservations before (I.freshStageLift first stage) = []) :
    historyObservations (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      historyObservations after stage := by
  rw [referenceSuffixHistoryJoin]
  simp only [historyObservations, List.filterMap_append] at hbefore ⊢
  rw [hbefore, List.nil_append]
  exact historyObservations_referenceSuffixLift I first _ after stage

theorem historyWrite_referenceSuffixJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage)
    (hbefore : historyWrite before (I.freshStageLift first stage) = none) :
    historyWrite (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      (historyWrite after stage).map (fun pair => (pair.1, (historyActions before).length + pair.2)) := by
  have hn : before.filterMap (eventWrite (I.freshStageLift first stage)) = [] := List.getLast?_eq_none_iff.mp hbefore
  rw [referenceSuffixHistoryJoin]
  simp only [historyWrite, List.filterMap_append, hn, List.nil_append]
  exact historyWrite_referenceSuffixLift I first _ after stage

theorem historyReport_referenceSuffixJoin (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage)
    (hbefore : historyReport before (I.freshStageLift first stage) = none) :
    historyReport (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      (historyReport after stage).map (fun pair => (pair.1, (historyActions before).length + pair.2)) := by
  have hn : before.filterMap (eventReport (I.freshStageLift first stage)) = [] := List.getLast?_eq_none_iff.mp hbefore
  rw [referenceSuffixHistoryJoin]
  simp only [historyReport, List.filterMap_append, hn, List.nil_append]
  exact historyReport_referenceSuffixLift I first _ after stage

def referenceSuffixCacheJoin (I : Instance) (first : ℕ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first)) : ReferenceReplayCache I where
  seen := referenceSuffixHistoryJoin I first base.seen cache.seen
  entryHistory := referenceSuffixHistoryJoin I first base.seen cache.entryHistory
  events := base.events ++ cache.events
  phase := referenceSuffixPhaseLift I first cache.phase
  halted := cache.halted

/-- Public algebraic base facts, supplied below from genuine first entries. -/
structure ReferenceSuffixBase (I : Instance) (first : ℕ) (budget risk : ℚ) (base : ReferenceReplayCache I) : Prop where
  bound : first ≤ I.stageCount
  cursor : historyCursor base.seen = first
  count : base.events.length = first
  snapshot : base.entryHistory = base.seen
  testing : base.phase = .testing
  active : base.halted = false
  riskPath : referenceReplayRisk budget base = some risk
  valid : ReferenceBudgetValid risk
  observations : ∀ stage : (I.freshSuffix first).Stage,
    historyObservations base.seen (I.freshStageLift first stage) = []
  written : ∀ stage : (I.freshSuffix first).Stage,
    historyWrite base.seen (I.freshStageLift first stage) = none
  reported : ∀ stage : (I.freshSuffix first).Stage,
    historyReport base.seen (I.freshStageLift first stage) = none

theorem referenceSuffixCacheJoin_risk (I : Instance) (first : ℕ) (budget risk : ℚ)
    (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceReplayRisk budget (referenceSuffixCacheJoin I first base cache) = referenceReplayRisk (2 * risk) cache :=
  referenceBudgetPath_restart budget risk base.events cache.events hbase.riskPath

theorem referenceSuffixCacheJoin_stage (I : Instance) (first : ℕ) (budget risk : ℚ)
    (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceReplayStage I (referenceSuffixCacheJoin I first base cache) =
      (referenceReplayStage (I.freshSuffix first) cache).map (I.freshStageLift first) := by
  have hc : historyCursor (referenceSuffixCacheJoin I first base cache).seen = first + historyCursor cache.seen := by
    change historyCursor (referenceSuffixHistoryJoin I first base.seen cache.seen) = _
    rw [historyCursor_referenceSuffixJoin, hbase.cursor]
  unfold referenceReplayStage
  split_ifs with hg hl hl
  · simp only [Option.map_some]
    congr 1
    apply Fin.ext
    exact hc
  · have hlen := I.freshSuffix_stageCount first
    have hh : first + historyCursor cache.seen < I.stageCount := hc ▸ hg
    omega
  · have hlen := I.freshSuffix_stageCount first
    have hh : first + historyCursor cache.seen < I.stageCount := by omega
    exact (hg (hc.symm ▸ hh)).elim
  · rfl

theorem referenceSuffixCacheJoin_kind (I : Instance) (first : ℕ) (available : Finset I.Tool)
    (budget risk : ℚ) (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceAvailableKind I available (referenceSuffixCacheJoin I first base cache) =
      referenceAvailableKind (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) cache := by
  simp only [referenceAvailableKind, referenceSuffixCacheJoin_stage I first budget risk base cache hbase]
  cases hs : referenceReplayStage (I.freshSuffix first) cache with
  | none => rfl
  | some stage =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    change referenceAvailableRankCase I available (I.freshStageLift first stage)
      (historyUsed (referenceSuffixHistoryJoin I first base.seen cache.entryHistory)) = _
    rw [historyUsed_referenceSuffixJoin]
    exact (referenceAvailableRankCase_freshSuffix I first available (historyUsed base.seen)
      (historyUsed (I := I.freshSuffix first) cache.entryHistory) stage).symm

theorem referenceSuffixCacheJoin_target (I : Instance) (first : ℕ) (available : Finset I.Tool)
    (budget risk : ℚ) (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceAvailableCacheTarget I available budget (referenceSuffixCacheJoin I first base cache) =
      referenceAvailableCacheTarget (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache := by
  have hphase := referenceSuffixPhaseLift_testing I first cache.phase
  have hcount : (referenceSuffixCacheJoin I first base cache).events.length ≤ I.stageCount ↔
      cache.events.length ≤ (I.freshSuffix first).stageCount := by
    change (base.events ++ cache.events).length ≤ I.stageCount ↔ _
    rw [List.length_append, hbase.count, I.freshSuffix_stageCount]
    have hb := hbase.bound
    omega
  unfold referenceAvailableCacheTarget
  have hguard : ((referenceSuffixCacheJoin I first base cache).halted ||
      decide ((referenceSuffixCacheJoin I first base cache).phase ≠ .testing)) =
      (cache.halted || decide (cache.phase ≠ .testing)) := by
    change (cache.halted || decide (referenceSuffixPhaseLift I first cache.phase ≠ .testing)) = _
    rw [decide_eq_decide.mpr (not_congr hphase)]
  rw [hguard, referenceSuffixCacheJoin_kind I first available budget risk base cache hbase,
    referenceSuffixCacheJoin_risk I first budget risk base cache hbase]
  simp only [hcount]

theorem referenceSuffixCacheJoin_correct (I : Instance) (first : ℕ) (budget risk : ℚ)
    (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) :
    referenceReplayCorrect (referenceSuffixCacheJoin I first base cache) (I.freshStageLift first stage) =
      referenceReplayCorrect cache stage := by
  unfold referenceReplayCorrect
  change (match historyWrite (referenceSuffixHistoryJoin I first base.seen cache.seen) (I.freshStageLift first stage),
      historyReport (referenceSuffixHistoryJoin I first base.seen cache.seen) (I.freshStageLift first stage) with
    | some (bit, serial), some (truth, reported) => decide (bit = truth ∧ reported = serial)
    | _, _ => false) = _
  rw [historyWrite_referenceSuffixJoin I first base.seen cache.seen stage (hbase.written stage),
    historyReport_referenceSuffixJoin I first base.seen cache.seen stage (hbase.reported stage)]
  cases hw : historyWrite cache.seen stage with
  | none => rfl
  | some written =>
    cases hr : historyReport cache.seen stage with
    | none => rfl
    | some report => simp only [Option.map_some, Nat.add_left_cancel_iff]

theorem referenceSuffixCacheJoin_mismatch (I : Instance) (first : ℕ) (budget risk : ℚ)
    (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage)
    (handle : MismatchHandle (I.freshSuffix first)) :
    referenceReplayMismatch (referenceSuffixCacheJoin I first base cache) (I.freshStageLift first stage)
      (referenceSuffixHandleLift I first (historyActions base.seen).length handle) =
      referenceReplayMismatch cache stage handle := by
  unfold referenceReplayMismatch
  change (match historyWrite (referenceSuffixHistoryJoin I first base.seen cache.seen) (I.freshStageLift first stage),
      historyReport (referenceSuffixHistoryJoin I first base.seen cache.seen) (I.freshStageLift first stage) with
    | some (bit, serial), some (truth, reported) => decide (bit ≠ truth ∧
        (referenceSuffixHandleLift I first (historyActions base.seen).length handle).stage = I.freshStageLift first stage ∧
        (referenceSuffixHandleLift I first (historyActions base.seen).length handle).writeSerial = serial ∧ reported = serial)
    | _, _ => false) = _
  rw [historyWrite_referenceSuffixJoin I first base.seen cache.seen stage (hbase.written stage),
    historyReport_referenceSuffixJoin I first base.seen cache.seen stage (hbase.reported stage)]
  cases hw : historyWrite cache.seen stage with
  | none => rfl
  | some written =>
    cases hr : historyReport cache.seen stage with
    | none => rfl
    | some report =>
      simp only [Option.map_some, referenceSuffixHandleLift, (freshStageLift_injective I first).eq_iff,
        Nat.add_left_cancel_iff]

theorem referenceSuffixCacheJoin_observation (I : Instance) (first : ℕ)
    (base : ReferenceReplayCache I) (cache : ReferenceReplayCache (I.freshSuffix first))
    (event : VisibleEvent (I.freshSuffix first)) :
    referenceSuffixCacheJoin I first base {cache with seen := cache.seen ++ [event]} =
      {referenceSuffixCacheJoin I first base cache with seen :=
        (referenceSuffixCacheJoin I first base cache).seen ++
          [referenceSuffixEventLift I first (historyActions base.seen).length event]} := by
  simp only [referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
    List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem referenceSuffixCacheJoin_step_observation (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (symbol : ℕ) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.observation stage symbol)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.observation stage symbol)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have htarget := referenceSuffixCacheJoin_target I first available budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_testing I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      have hp : (referenceSuffixCacheJoin I first base cache).phase = .testing ↔ cache.phase = .testing := hphase
      have he : (input.freshSuffix first).experiment stage = input.experiment (I.freshStageLift first stage) := input.freshSuffix_experiment first stage
      rw [← he, htarget]
      simp only [(freshStageLift_injective I first).eq_iff, hp]
      split_ifs with hg
      · simpa only [Option.map_some, referenceSuffixCacheJoin, hhcache, referenceSuffixEventLift] using
          congrArg some (referenceSuffixCacheJoin_observation I first base cache (.observation stage symbol)).symm
      · rfl

theorem referenceSuffixCacheJoin_step_write (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (bit : Bool) (serial : ℕ) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.wrote stage bit serial)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.wrote stage bit serial)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hkind := referenceSuffixCacheJoin_kind I first available budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase : (referenceSuffixCacheJoin I first base cache).phase = .testing ↔ cache.phase = .testing :=
    referenceSuffixPhaseLift_testing I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  have ha : (historyActions (referenceSuffixCacheJoin I first base cache).seen).length =
      (historyActions base.seen).length + (historyActions cache.seen).length := historyActions_referenceSuffixJoin_length I first base.seen cache.seen
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hkind, hrisk]
      cases hk : referenceAvailableKind (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) cache with
      | none => rfl
      | some kind =>
        simp only [Option.bind_some]
        cases hr : referenceReplayRisk (2 * risk) cache with
        | none => rfl
        | some currentRisk =>
          simp only [Option.bind_some, ha, Nat.add_left_cancel_iff, (freshStageLift_injective I first).eq_iff, hphase]
          split_ifs with hg
          · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
              List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
              referenceSuffixEventLift]
          · rfl

theorem referenceSuffixCacheJoin_step_report (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (truth : Bool) (serial : ℕ) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.report stage truth serial)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.report stage truth serial)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hkind := referenceSuffixCacheJoin_kind I first available budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase : (referenceSuffixCacheJoin I first base cache).phase = .written ↔ cache.phase = .written :=
    referenceSuffixPhaseLift_written I first cache.phase
  have hcount : (referenceSuffixCacheJoin I first base cache).events.length < I.stageCount ↔
      cache.events.length < (I.freshSuffix first).stageCount := by
    change (base.events ++ cache.events).length < I.stageCount ↔ _
    rw [List.length_append, hbase.count, I.freshSuffix_stageCount]
    have hb := hbase.bound
    omega
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hkind, hrisk]
      rw [show historyWrite (referenceSuffixCacheJoin I first base cache).seen (I.freshStageLift first current) =
          (historyWrite cache.seen current).map (fun pair => (pair.1, (historyActions base.seen).length + pair.2)) from
        historyWrite_referenceSuffixJoin I first base.seen cache.seen current (hbase.written current)]
      cases hw : historyWrite cache.seen current with
      | none => rfl
      | some written =>
        simp only [Option.map_some, Option.bind_some]
        cases hk : referenceAvailableKind (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) cache with
        | none => rfl
        | some kind =>
          simp only [Option.bind_some]
          cases hr : referenceReplayRisk (2 * risk) cache with
          | none => rfl
          | some currentRisk =>
            simp only [Option.bind_some, Nat.add_left_cancel_iff, (freshStageLift_injective I first).eq_iff, hphase, hcount]
            split_ifs with hg
            · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
                List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
                referenceSuffixEventLift]
            · rfl

theorem referenceSuffixCacheJoin_step_advance (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.advanced stage)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.advanced stage)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_reported I first cache.phase
  have hexecuted : (∃ tool : I.Tool, referenceSuffixPhaseLift I first cache.phase = .executed tool) ↔
      ∃ tool : (I.freshSuffix first).Tool, cache.phase = .executed tool := by
    cases cache.phase <;> simp [referenceSuffixPhaseLift]
    exact ⟨_, rfl⟩
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hrisk]
      cases hr : referenceReplayRisk (2 * risk) cache with
      | none => rfl
      | some currentRisk =>
        simp only [Option.bind_some, (freshStageLift_injective I first).eq_iff,
          referenceSuffixCacheJoin_correct I first budget risk base cache hbase current]
        change (if stage = current ∧ ((referenceSuffixPhaseLift I first cache.phase = .reported ∧ referenceReplayCorrect cache current = true) ∨
            ∃ tool, referenceSuffixPhaseLift I first cache.phase = .executed tool) then _ else _) = _
        simp only [hphase, hexecuted]
        split_ifs with hg
        · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
            List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
            referenceSuffixEventLift]
        · rfl

theorem referenceSuffixCacheJoin_step_execute (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (handle : MismatchHandle (I.freshSuffix first)) (tool : I.Tool) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.executed handle tool)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.executed handle tool)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_allocated I first cache.phase tool
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some,
        referenceSuffixCacheJoin_mismatch I first budget risk base cache hbase current handle]
      change (if referenceSuffixPhaseLift I first cache.phase = .allocated tool ∧ referenceReplayMismatch cache current handle = true then _ else _) = _
      simp only [hphase]
      split_ifs with hg
      · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
          List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
          referenceSuffixEventLift]
      · rfl

theorem referenceSuffixCacheJoin_step_allocate (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (handle : MismatchHandle (I.freshSuffix first)) (tool : I.Tool) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.committed handle tool)) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.committed handle tool)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_reported I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, referenceSuffixEventLift, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none => rfl
    | some current =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hrisk]
      cases hr : referenceReplayRisk (2 * risk) cache with
      | none => rfl
      | some currentRisk =>
        simp only [Option.bind_some, referenceSuffixCacheJoin_mismatch I first budget risk base cache hbase current handle]
        have hused : historyUsed (referenceSuffixCacheJoin I first base cache).seen =
            historyUsed base.seen ∪ historyUsed (I := I.freshSuffix first) cache.seen := historyUsed_referenceSuffixJoin I first base.seen cache.seen
        have hentryUsed : historyUsed (referenceSuffixCacheJoin I first base cache).entryHistory =
            historyUsed base.seen ∪ historyUsed (I := I.freshSuffix first) cache.entryHistory := historyUsed_referenceSuffixJoin I first base.seen cache.entryHistory
        rw [hused, hentryUsed, ← referenceAvailableRepairTool_freshSuffix I first available (historyUsed base.seen)
          (historyUsed (I := I.freshSuffix first) cache.entryHistory) current, I.freshSuffix_eligible first current]
        have hcondition :
            ((referenceSuffixCacheJoin I first base cache).phase = .reported ∧ referenceReplayMismatch cache current handle = true ∧
              tool ∈ I.eligible (I.freshStageLift first current) ∧ tool ∉ historyUsed base.seen ∪ historyUsed (I := I.freshSuffix first) cache.seen ∧
              tool ∈ available ∧ referenceAvailableRepairTool (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) current
                (historyUsed cache.entryHistory) = some tool) ↔
            (cache.phase = .reported ∧ referenceReplayMismatch cache current handle = true ∧
              tool ∈ I.eligible (I.freshStageLift first current) ∧ tool ∉ historyUsed cache.seen ∧
              tool ∈ available \ historyUsed (I := I) base.seen ∧ referenceAvailableRepairTool (I.freshSuffix first)
                (available \ historyUsed (I := I) base.seen) current (historyUsed cache.entryHistory) = some tool) := by
          constructor
          · rintro ⟨hph, hm, he, hu, ha, hpick⟩
            refine ⟨hphase.mp hph, hm, he, ?_, ?_, hpick⟩
            · intro ht
              exact hu (Finset.mem_union_right _ ht)
            · exact Finset.mem_sdiff.mpr ⟨ha, fun ht => hu (Finset.mem_union_left _ ht)⟩
          · rintro ⟨hph, hm, he, hu, ha, hpick⟩
            refine ⟨hphase.mpr hph, hm, he, ?_, (Finset.mem_sdiff.mp ha).1, hpick⟩
            intro ht
            rcases Finset.mem_union.mp ht with hold | hnew
            · exact (Finset.mem_sdiff.mp ha).2 hold
            · exact hu hnew
        split_ifs with hg hc
        · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
            List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
            referenceSuffixEventLift]
        · exact False.elim (hc (hcondition.mp hg))
        · rename_i hc
          exact False.elim (hg (hcondition.mpr hc))
        · rfl

theorem referenceSuffixCacheJoin_step_stop (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache) .stopped =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache .stopped).map (referenceSuffixCacheJoin I first base) := by
  have hphase := referenceSuffixPhaseLift_testing I first cache.phase
  have hc : historyCursor (referenceSuffixCacheJoin I first base cache).seen = I.stageCount ↔
      historyCursor cache.seen = (I.freshSuffix first).stageCount := by
    change historyCursor (referenceSuffixHistoryJoin I first base.seen cache.seen) = I.stageCount ↔ _
    rw [historyCursor_referenceSuffixJoin, hbase.cursor, I.freshSuffix_stageCount]
    have hb := hbase.bound
    omega
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false, hc]
    change (if historyCursor cache.seen = (I.freshSuffix first).stageCount ∧ referenceSuffixPhaseLift I first cache.phase = .testing then _ else _) = _
    simp only [hphase]
    split_ifs with hg
    · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixEventLift]
    · rfl

theorem referenceSuffixCacheJoin_step_abandon (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first)) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache) .abandoned =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache .abandoned).map (referenceSuffixCacheJoin I first base) := by
  have hphase := referenceSuffixPhaseLift_written I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold referenceAvailableStep
  rw [hh]
  cases hhcache : cache.halted with
  | true => simp only [ite_true, Option.map_none]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    change (if referenceSuffixPhaseLift I first cache.phase ≠ .written then _ else _) = _
    simp only [not_congr hphase]
    split_ifs with hg <;> first
      | contradiction
      | rfl
      | simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
          List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixEventLift]

/-- Every response branch of the actual availability-aware parser commutes
with the concrete visible history/serial restart. No favorable-path filter. -/
theorem referenceSuffixCacheJoin_step (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (event : VisibleEvent (I.freshSuffix first)) :
    referenceAvailableStep input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length event) =
      (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache event).map
        (referenceSuffixCacheJoin I first base) := by
  cases event with
  | observation stage symbol => exact referenceSuffixCacheJoin_step_observation input first available budget risk base cache hbase stage symbol
  | wrote stage bit serial => exact referenceSuffixCacheJoin_step_write input first available budget risk base cache hbase stage bit serial
  | report stage truth serial => exact referenceSuffixCacheJoin_step_report input first available budget risk base cache hbase stage truth serial
  | committed handle tool => exact referenceSuffixCacheJoin_step_allocate input first available budget risk base cache hbase handle tool
  | executed handle tool => exact referenceSuffixCacheJoin_step_execute input first available budget risk base cache hbase handle tool
  | advanced stage => exact referenceSuffixCacheJoin_step_advance input first available budget risk base cache hbase stage
  | stopped => exact referenceSuffixCacheJoin_step_stop input first available budget risk base cache hbase
  | abandoned => exact referenceSuffixCacheJoin_step_abandon input first available budget risk base cache

theorem referenceSuffixCacheJoin_fold (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first)) :
    (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
        (referenceAvailableStep input available budget) (referenceSuffixCacheJoin I first base cache) =
      (history.foldlM (referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)) cache).map
        (referenceSuffixCacheJoin I first base) := by
  induction history generalizing cache with
  | nil => rfl
  | cons event rest ih =>
    simp only [referenceSuffixHistoryLift, List.map_cons, List.foldlM_cons]
    rw [referenceSuffixCacheJoin_step input first available budget risk base cache hbase event]
    cases hs : referenceAvailableStep (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache event with
    | none => rfl
    | some next =>
      simp only [Option.map_some]
      exact ih next

theorem referenceSuffixCacheJoin_initial (I : Instance) (first : ℕ) (budget risk : ℚ)
    (base : ReferenceReplayCache I) (hbase : ReferenceSuffixBase I first budget risk base) :
    referenceSuffixCacheJoin I first base (referenceReplayInitial (I.freshSuffix first)) = base := by
  cases base with
  | mk seen entry events phase halted =>
    have he := hbase.snapshot
    have hp := hbase.testing
    have hh := hbase.active
    simp only [referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift, referenceReplayInitial,
      referenceSuffixPhaseLift, List.map_nil, List.append_nil]
    simp only at he hp hh
    rw [he, hp, hh]

/-- The entire accepted suffix grammar, including reports, repairs and
terminal/failure responses, is accepted after the old actual visible entry.
This is a full parser transport, not merely equality of the first action. -/
theorem referenceSuffix_replay_join (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : referenceAvailableReplay input available budget base.seen = some base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hparse : referenceAvailableReplay (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) history = some cache) :
    referenceAvailableReplay input available budget (referenceSuffixHistoryJoin I first base.seen history) =
      some (referenceSuffixCacheJoin I first base cache) := by
  have hb := referenceAvailableReplay_some_spec input available budget base.seen base hparseBase
  have hf := referenceAvailableReplay_some_spec (input.freshSuffix first) (available \ historyUsed (I := I) base.seen)
    (2 * risk) history cache hparse
  have hfold : (referenceSuffixHistoryJoin I first base.seen history).foldlM
      (referenceAvailableStep input available budget) (referenceReplayInitial I) = some (referenceSuffixCacheJoin I first base cache) := by
    rw [referenceSuffixHistoryJoin, List.foldlM_append, hb.2.1]
    change (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
      (referenceAvailableStep input available budget) base = _
    calc
      _ = (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
          (referenceAvailableStep input available budget)
          (referenceSuffixCacheJoin I first base (referenceReplayInitial (I.freshSuffix first))) :=
        congrArg (fun start => (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
          (referenceAvailableStep input available budget) start) (referenceSuffixCacheJoin_initial I first budget risk base hbase).symm
      _ = _ := (referenceSuffixCacheJoin_fold input first available budget risk base hbase history
        (referenceReplayInitial (I.freshSuffix first))).trans (by rw [hf.2.1]; rfl)
  have hfinal : (referenceSuffixCacheJoin I first base cache).phase ≠ .written ∧
      (referenceSuffixCacheJoin I first base cache).events.length ≤ I.stageCount ∧
      historyCursor (referenceSuffixCacheJoin I first base cache).seen ≤ I.stageCount ∧
      (referenceSuffixCacheJoin I first base cache).seen = referenceSuffixHistoryJoin I first base.seen history := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun hw => hf.2.2.1 ((referenceSuffixPhaseLift_written I first cache.phase).mp hw)
    · change (base.events ++ cache.events).length ≤ I.stageCount
      rw [List.length_append, hbase.count]
      have hlen := hf.2.2.2.1
      rw [I.freshSuffix_stageCount] at hlen
      have hbound := hbase.bound
      omega
    · change historyCursor (referenceSuffixHistoryJoin I first base.seen cache.seen) ≤ I.stageCount
      rw [historyCursor_referenceSuffixJoin, hbase.cursor]
      have hc := hf.2.2.2.2.1
      rw [I.freshSuffix_stageCount] at hc
      have hbound := hbase.bound
      omega
    · exact congrArg (referenceSuffixHistoryJoin I first base.seen) hf.2.2.2.2.2
  simp only [referenceAvailableReplay, hb.1]
  rw [hfold]
  exact ite_eq_left hfinal

private def suffixWordFromSymbols (E : BinaryExperiment) (symbols : List ℕ)
    (valid : ∀ symbol ∈ symbols, symbol < E.alphabetSize) : E.StoppedWord :=
  ⟨symbols.length, fun k => ⟨symbols[k.val], valid _ (List.getElem_mem k.isLt)⟩⟩

private theorem suffixWordFromSymbols_congr (E F : BinaryExperiment) (he : E = F)
    (left right : List ℕ) (hword : left = right)
    (hl : ∀ symbol ∈ left, symbol < E.alphabetSize) (hr : ∀ symbol ∈ right, symbol < F.alphabetSize) :
    HEq (suffixWordFromSymbols E left hl) (suffixWordFromSymbols F right hr) := by
  subst F
  subst right
  rfl

private theorem suffixWordData_congr (E F : BinaryExperiment) (he : E = F) (p : ℚ)
    (left : E.StoppedWord) (right : F.StoppedWord) (hw : HEq left right) :
    (E.rationalWordHits p left, E.rationalWordMAP left) = (F.rationalWordHits p right, F.rationalWordMAP right) := by
  subst F
  cases hw
  rfl

/-- The full finite-word testing computation commutes with the suffix
restart, including inclusive hit before review and the MAP write bit. -/
theorem referenceSuffix_testingAction (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) :
    referenceTestingAction input available budget none (referenceSuffixCacheJoin I first base cache) (I.freshStageLift first stage) =
      referenceSuffixActionLift I first (historyActions base.seen).length
        (referenceTestingAction (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none cache stage) := by
  have hk := referenceSuffixCacheJoin_kind I first available budget risk base cache hbase
  have ht := referenceSuffixCacheJoin_target I first available budget risk base cache hbase
  have he := input.freshSuffix_experiment first stage
  have ho : historyObservations (referenceSuffixCacheJoin I first base cache).seen (I.freshStageLift first stage) =
      historyObservations cache.seen stage := historyObservations_referenceSuffixJoin I first base.seen cache.seen stage (hbase.observations stage)
  have hv : (∀ symbol ∈ historyObservations (referenceSuffixCacheJoin I first base cache).seen (I.freshStageLift first stage),
      symbol < (input.experiment (I.freshStageLift first stage)).alphabetSize) ↔
      ∀ symbol ∈ historyObservations cache.seen stage, symbol < ((input.freshSuffix first).experiment stage).alphabetSize := by
    rw [ho, he]
  unfold referenceTestingAction
  rw [hk]
  cases hkind : referenceAvailableKind (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) cache with
  | none => rfl
  | some kind =>
    cases kind with
    | infiniteRank => rfl
    | noTool | finiteBad depth =>
      rw [ht]
      cases htarget : referenceAvailableCacheTarget (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache with
      | none => rfl
      | some p =>
        dsimp only
        by_cases hvalid : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < ((input.freshSuffix first).experiment stage).alphabetSize
        · have hglobal := hv.mpr hvalid
          rw [dite_eq_left hglobal, dite_eq_left hvalid]
          have hw : HEq
              (historyObservationWord input (referenceSuffixCacheJoin I first base cache).seen (I.freshStageLift first stage) hglobal)
              (historyObservationWord (input.freshSuffix first) cache.seen stage hvalid) :=
            suffixWordFromSymbols_congr _ _ he.symm _ _ ho hglobal hvalid
          have hd := suffixWordData_congr _ _ he.symm p _ _ hw
          have hh := congrArg Prod.fst hd
          have hm := congrArg Prod.snd hd
          dsimp only at hh hm
          rw [hh, hm]
          split_ifs <;> rfl
        · have hglobal : ¬ (∀ symbol ∈ historyObservations (referenceSuffixCacheJoin I first base cache).seen (I.freshStageLift first stage),
              symbol < (input.experiment (I.freshStageLift first stage)).alphabetSize) := fun h => hvalid (hv.mp h)
          rw [dite_eq_right hglobal, dite_eq_right hvalid]
          rfl

/-- Complete candidate-action homomorphism on accepted finite suffix
histories. This includes all phases; it does not yet assert Native.Step or
full run correspondence for the visible permission guards. -/
theorem referenceSuffix_candidateAction (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : referenceAvailableReplay input available budget base.seen = some base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hparse : referenceAvailableReplay (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) history = some cache) :
    referenceCandidateAction input available budget none (referenceSuffixHistoryJoin I first base.seen history) =
      referenceSuffixActionLift I first (historyActions base.seen).length
        (referenceCandidateAction (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none history) := by
  have hg := referenceSuffix_replay_join input first available budget risk base hbase hparseBase history cache hparse
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  simp only [referenceCandidateAction, hg, hparse, hh]
  cases hhalt : cache.halted with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, hstage]
    cases hs : referenceReplayStage (I.freshSuffix first) cache with
    | none =>
      simp only [Option.map_none]
      have hc : historyCursor (referenceSuffixHistoryJoin I first base.seen history) = I.stageCount ↔
          historyCursor history = (I.freshSuffix first).stageCount := by
        rw [historyCursor_referenceSuffixJoin, hbase.cursor, I.freshSuffix_stageCount]
        have hb := hbase.bound
        omega
      rw [if_congr hc rfl rfl]
      split_ifs <;> rfl
    | some stage =>
      simp only [Option.map_some]
      have hv : referenceVisibleHandle (referenceSuffixHistoryJoin I first base.seen history) (I.freshStageLift first stage) =
          (referenceVisibleHandle history stage).map (referenceSuffixHandleLift I first (historyActions base.seen).length) := by
        simp only [referenceVisibleHandle, historyWrite_referenceSuffixJoin I first base.seen history stage (hbase.written stage)]
        cases historyWrite history stage <;> rfl
      have hpick : referenceAvailableRepairTool I available (I.freshStageLift first stage)
          (historyUsed (referenceSuffixCacheJoin I first base cache).entryHistory) =
          referenceAvailableRepairTool (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) stage (historyUsed cache.entryHistory) := by
        change referenceAvailableRepairTool I available (I.freshStageLift first stage)
          (historyUsed (referenceSuffixHistoryJoin I first base.seen cache.entryHistory)) = _
        rw [historyUsed_referenceSuffixJoin]
        exact (referenceAvailableRepairTool_freshSuffix I first available (historyUsed base.seen)
          (historyUsed (I := I.freshSuffix first) cache.entryHistory) stage).symm
      have hp : (referenceSuffixCacheJoin I first base cache).phase = referenceSuffixPhaseLift I first cache.phase := rfl
      rw [hp]
      cases hphase : cache.phase with
      | testing => exact referenceSuffix_testingAction input first available budget risk base cache hbase stage
      | written => rfl
      | executed tool => rfl
      | allocated tool =>
        simp only [referenceSuffixPhaseLift, hv]
        cases referenceVisibleHandle history stage <;> rfl
      | reported =>
        simp only [referenceSuffixPhaseLift, referenceSuffixCacheJoin_correct I first budget risk base cache hbase stage,
          referenceSuffixCacheJoin_risk I first budget risk base cache hbase, hv, hpick]
        cases hc : referenceReplayCorrect cache stage with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases referenceReplayRisk (2 * risk) cache <;> cases referenceVisibleHandle history stage <;>
            cases referenceAvailableRepairTool (I.freshSuffix first) (available \ historyUsed (I := I) base.seen) stage (historyUsed cache.entryHistory) <;> rfl

/-- Every not-yet-entered port is still empty in the actual entry snapshot,
including the newly entered port itself. -/
theorem referenceEntry_unborn_queries {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history)
    (target : I.Stage) (htarget : stage.val ≤ target.val) :
    historyObservations history target = [] ∧ historyWrite history target = none ∧ historyReport history target = none := by
  by_cases hz : stage.val = 0
  · have he := entryHistory_stageZero input C .uncapped accounting (referenceRule input available budget none) stage hz sample
    have hh : history = [] := Option.some.inj (hentry.symm.trans he)
    subst history
    exact ⟨rfl, rfl, rfl⟩
  · let previous : I.Stage := ⟨stage.val - 1, by have hs := stage.isLt; omega⟩
    have hnext : stage.val = previous.val + 1 := by dsimp only [previous]; omega
    obtain ⟨n, s, next, hp, _, hs, haction, hhistory⟩ := referenceNextEntry_has_advance input C hearly accounting available budget
      sample previous stage hnext history hentry
    cases hs with
    | advance current live written resources =>
      have hfuture : s.cursor < target.val := by have hc := live.2; omega
      have hclean := prefix_future_port_clean input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp target hfuture
      have hr := (prefix_cursorInvariant input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp).future_reviews target hfuture
      have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) (n + 1)
          (record accounting s (.advance previous) [.advanced previous] (advanceLedger s previous) (s.cursor + 1) false) := by
        apply Prefix.next hp
        rw [haction]
        exact Step.advance s previous live written resources
      have hlength := prefix_historyObservations_length_toNat input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      have hwrite := prefix_historyWritten input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      have hreport := prefix_historyReport_early input C hearly .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      rw [hhistory] at hlength hwrite hreport
      refine ⟨?_, ?_, ?_⟩
      · apply List.eq_nil_of_length_eq_zero
        simpa only [record, advanceLedger, hr, ENat.toNat_zero] using hlength
      · have hw : historyWritten history target = none := by
          simpa only [record, advanceLedger, hclean.1] using hwrite
        cases hraw : historyWrite history target with
        | none => rfl
        | some pair => simp only [historyWritten, hraw, Option.map_some] at hw; cases hw
      · simpa only [record, advanceLedger, hclean.2.1, Option.map_none] using hreport

/-- All restart algebra facts are derived from the actual original entry,
not required as extra controller assumptions. -/
theorem referenceEntry_suffixBase {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ base risk, referenceAvailableReplay input available budget history = some base ∧ base.seen = history ∧
      referenceAvailableEntryRisk input available budget history = some risk ∧
      ReferenceSuffixBase I stage.val budget risk base := by
  obtain ⟨base, hp, hseen, hsnap, hphase, hactive, hcursor, hcount⟩ := referenceEntry_replay_snapshot input C hearly accounting
    available budget hbudget hsmall sample stage history hentry
  obtain ⟨_, risk, _, hr, hv, _⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget hbudget hsmall
    sample stage history hentry
  have hpath : referenceReplayRisk budget base = some risk := by
    simpa only [referenceAvailableEntryRisk, hp, Option.bind_eq_bind, Option.bind_some] using hr
  refine ⟨base, risk, hp, hseen, hr, ?_⟩
  refine ⟨stage.isLt.le, hcursor, hcount, hsnap.trans hseen.symm, hphase, hactive, hpath, hv, ?_, ?_, ?_⟩
  · intro current
    rw [hseen]
    exact (referenceEntry_unborn_queries input C hearly accounting available budget sample stage history hentry
      (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).1
  · intro current
    rw [hseen]
    exact (referenceEntry_unborn_queries input C hearly accounting available budget sample stage history hentry
      (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).2.1
  · intro current
    rw [hseen]
    exact (referenceEntry_unborn_queries input C hearly accounting available budget sample stage history hentry
      (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).2.2

/-- Actual-entry instantiation of the whole finite parser and all-phase
candidate homomorphism. Every base fact is proved from the original run. -/
theorem referenceEntry_fullReplay_transport {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ (base : ReferenceReplayCache I) (risk : ℚ), base.seen = history ∧
      referenceAvailableReplay input available budget history = some base ∧
      referenceAvailableEntryRisk input available budget history = some risk ∧ ReferenceBudgetValid risk ∧
      ∀ (after : List (VisibleEvent (I.freshSuffix stage.val))) (cache : ReferenceReplayCache (I.freshSuffix stage.val)),
        referenceAvailableReplay (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) after = some cache →
          referenceAvailableReplay input available budget (referenceSuffixHistoryJoin I stage.val history after) =
            some (referenceSuffixCacheJoin I stage.val base cache) ∧
          referenceCandidateAction input available budget none (referenceSuffixHistoryJoin I stage.val history after) =
            referenceSuffixActionLift I stage.val (historyActions history).length
              (referenceCandidateAction (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none after) := by
  obtain ⟨base, risk, hp, hseen, hr, hb⟩ := referenceEntry_suffixBase input C hearly accounting available budget hbudget hsmall
    sample stage history hentry
  have hpbase : referenceAvailableReplay input available budget base.seen = some base := by rw [hseen]; exact hp
  refine ⟨base, risk, hseen, hp, hr, hb.valid, ?_⟩
  intro after cache hafter
  have hlocal : referenceAvailableReplay (input.freshSuffix stage.val) (available \ historyUsed (I := I) base.seen) (2 * risk) after = some cache := by
    simpa only [hseen] using hafter
  exact ⟨by simpa only [hseen] using referenceSuffix_replay_join input stage.val available budget risk base hb hpbase after cache hlocal,
    by simpa only [hseen] using referenceSuffix_candidateAction input stage.val available budget risk base hb hpbase after cache hlocal⟩

/-- The original world's suffix restriction, with the entire experiment
pulled back. This is analysis data, never passed to the executable rule. -/
def referenceSuffixWorld (input : StatisticalInput I) (first : ℕ) (world : input.World) : (input.freshSuffix first).World :=
  fun stage => ((world (I.freshStageLift first stage)).1,
    Eq.mpr (congrArg (fun E : BinaryExperiment => E.Tape) (input.freshSuffix_experiment first stage))
      (world (I.freshStageLift first stage)).2)

/-- Complete B18 execution-and-observation transport, proved by
`referenceSuffixRunTransport` below from the original actual entry.
The original Seed universe, available set, public budget and every
failed/abandoned/infinite path remain quantified.
No hidden state is made a seed, and no performance clause is a Policy field. -/
def ReferenceSuffixRunTransport (input : StatisticalInput I) (Seed : Type*) : Prop :=
  ∀ (C : Contract I), C.IsCurrentAllocation → ∀ (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ), 0 < budget → budget ≤ 1 / 2 →
      ∀ (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I)),
        entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history →
          ∃ (risk : ℚ) (n : ℕ), referenceAvailableEntryRisk input available budget history = some risk ∧
            ReferenceBudgetValid risk ∧
            (run input C .uncapped accounting (referenceRule input available budget none) sample n).cursor = stage.val ∧
            (∀ k < n, (run input C .uncapped accounting (referenceRule input available budget none) sample k).cursor ≠ stage.val) ∧
            (run input C .uncapped accounting (referenceRule input available budget none) sample n).history = history ∧
            (let childInput := input.freshSuffix stage.val
             let childRule : PolicyRule (I.freshSuffix stage.val) Seed :=
               referenceRule childInput (available \ historyUsed (I := I) history) (2 * risk) none
             let childSample : Seed × childInput.World := (sample.1, referenceSuffixWorld input stage.val sample.2)
             (∀ k : ℕ,
               let parent := run input C .uncapped accounting (referenceRule input available budget none) sample (n + k)
               let child := run childInput (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
                 (zeroNormalAccounting (I.freshSuffix stage.val)) childRule childSample k
               parent.history = referenceSuffixHistoryJoin I stage.val history child.history ∧
               parent.cursor = stage.val + child.cursor ∧
               parent.clock = (historyActions history).length + child.clock ∧
               parent.halted = child.halted ∧
               ∀ target : (I.freshSuffix stage.val).Stage,
                 parent.ledger.reviews (I.freshStageLift stage.val target) = child.ledger.reviews target) ∧
             runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) stage.val sample =
               runObservationBill childInput (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
                 (zeroNormalAccounting (I.freshSuffix stage.val)) childRule childSample)

/-- Only the public returned-action view is compared, never whole ledgers
or their hidden truth/normal-call fields. -/
structure ReferenceSuffixView (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (parent : State I) (child : State (I.freshSuffix first)) : Prop where
  history : parent.history = referenceSuffixHistoryJoin I first before child.history
  cursor : parent.cursor = first + child.cursor
  clock : parent.clock = (historyActions before).length + child.clock
  halted : parent.halted = child.halted

theorem ReferenceSuffixView.record {first : ℕ} {before : List (VisibleEvent I)}
    {parent : State I} {child : State (I.freshSuffix first)} (view : ReferenceSuffixView I first before parent child)
    (accounting : NormalAccounting I) (childAccounting : NormalAccounting (I.freshSuffix first))
    (action : Action (I.freshSuffix first)) (responses : List (VisibleEvent (I.freshSuffix first)))
    (parentLedger : Ledger I) (childLedger : Ledger (I.freshSuffix first)) (parentCursor childCursor : ℕ)
    (hcursor : parentCursor = first + childCursor) (halted : Bool) :
    ReferenceSuffixView I first before
      (record accounting parent (referenceSuffixActionLift I first (historyActions before).length action)
        (referenceSuffixHistoryLift I first (historyActions before).length responses) parentLedger parentCursor halted)
      (record childAccounting child action responses childLedger childCursor halted) := by
  constructor
  · change parent.history ++ referenceSuffixHistoryLift I first (historyActions before).length responses =
      referenceSuffixHistoryJoin I first before (child.history ++ responses)
    rw [view.history, referenceSuffixHistoryJoin_append]
  · exact hcursor
  · change parent.clock + 1 = (historyActions before).length + (child.clock + 1)
    rw [view.clock]
    omega
  · rfl

theorem ReferenceSuffixView.stop {first : ℕ} {before : List (VisibleEvent I)}
    {parent : State I} {child : State (I.freshSuffix first)} (view : ReferenceSuffixView I first before parent child)
    (abandon : Bool) : ReferenceSuffixView I first before (stopState parent abandon) (stopState child abandon) := by
  constructor
  · change parent.history ++ [if abandon then .abandoned else .stopped] =
      referenceSuffixHistoryJoin I first before (child.history ++ [if abandon then .abandoned else .stopped])
    rw [view.history, referenceSuffixHistoryJoin_append]
    cases abandon <;> rfl
  · exact view.cursor
  · change parent.clock + 1 = (historyActions before).length + (child.clock + 1)
    rw [view.clock]
    omega
  · rfl

/-- Actual legal steps on both sides preserve the public view. In particular
write transports the WHOLE early wrote/report packet as one native action.
The equal counts/truths/tape letters used here are derived from actual run
prefixes in the following run proof, not imposed on a Policy. -/
theorem referenceSuffix_step_view (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (childC : Contract (I.freshSuffix first))
    (hearly : C.reporting = .early) (hchildEarly : childC.reporting = .early)
    (accounting : NormalAccounting I) (childAccounting : NormalAccounting (I.freshSuffix first))
    (tapes : ReviewTapes input) (childTapes : ReviewTapes (input.freshSuffix first))
    (before : List (VisibleEvent I)) {parent nextParent : State I} {child nextChild : State (I.freshSuffix first)}
    {action : Action (I.freshSuffix first)}
    (view : ReferenceSuffixView I first before parent child)
    (counts : ∀ stage, parent.ledger.reviews (I.freshStageLift first stage) = child.ledger.reviews stage)
    (truths : ∀ stage, parent.ledger.truth (I.freshStageLift first stage) = child.ledger.truth stage)
    (letters : ∀ stage k, (tapes (I.freshStageLift first stage) k).val = (childTapes stage k).val)
    (hp : Step input C .uncapped accounting tapes parent
      (referenceSuffixActionLift I first (historyActions before).length action) nextParent)
    (hc : Step (input.freshSuffix first) childC .uncapped childAccounting childTapes child action nextChild) :
    ReferenceSuffixView I first before nextParent nextChild := by
  cases hc with
  | review stage live port resources =>
    cases hp with
    | review current plive pport presources =>
      have hv := view.record accounting childAccounting (.review stage)
        [.observation stage (childTapes stage (child.ledger.reviews stage).toNat).val]
        (reviewLedger parent (I.freshStageLift first stage)) (reviewLedger child stage)
        parent.cursor child.cursor view.cursor false
      simpa only [referenceSuffixHistoryLift, List.map_cons, List.map_nil, referenceSuffixEventLift,
        referenceSuffixActionLift, counts stage, letters stage] using hv
  | write stage bit live port resources =>
    cases hp with
    | write current pbit plive pport presources =>
      have hpacket : writeResponses C parent (I.freshStageLift first stage) bit =
          referenceSuffixHistoryLift I first (historyActions before).length (writeResponses childC child stage bit) := by
        simp only [writeResponses, hearly, hchildEarly, ite_true, writeLedger, referenceSuffixHistoryLift,
          List.map_append, List.map_cons, List.map_nil, referenceSuffixEventLift, view.clock, truths stage]
      have hv := view.record accounting childAccounting (.write stage bit) (writeResponses childC child stage bit)
        (reportedWriteLedger C parent (I.freshStageLift first stage) bit) (reportedWriteLedger childC child stage bit)
        parent.cursor child.cursor view.cursor false
      rw [← hpacket] at hv
      exact hv
  | allocate handle tool active valid compatible unused unallocated window resources =>
    cases hp with
    | allocate phandle ptool pactive pvalid pcompatible punused punallocated pwindow presources =>
      have hv := view.record accounting childAccounting (.allocate handle tool) [.committed handle tool]
        (allocateLedger parent (referenceSuffixHandleLift I first (historyActions before).length handle) tool)
        (allocateLedger child handle tool) parent.cursor child.cursor view.cursor false
      exact hv
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    cases hp with
    | execute phandle ptool pactive pvalid pcompatible pcommitted punused puncorrected pwindow presources =>
      have hv := view.record accounting childAccounting (.execute handle tool) [.executed handle tool]
        (executeLedger parent (referenceSuffixHandleLift I first (historyActions before).length handle) tool)
        (executeLedger child handle tool) parent.cursor child.cursor view.cursor false
      exact hv
  | advance stage live written resources =>
    cases hp with
    | advance current plive pwritten presources =>
      exact view.record accounting childAccounting (.advance stage) [.advanced stage]
        (advanceLedger parent (I.freshStageLift first stage)) (advanceLedger child stage)
        (parent.cursor + 1) (child.cursor + 1) (by rw [view.cursor]; omega) false
  | stop active =>
    cases hp with
    | stop pactive => exact view.stop false
  | abandon active =>
    cases hp with
    | abandon pactive => exact view.stop true

theorem referenceSuffix_rule_of_prefixes {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (base : ReferenceReplayCache I) (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : referenceAvailableReplay input available budget base.seen = some base)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first)) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (childTruth : (I.freshSuffix first).Stage → Bool) (childTapes : ReviewTapes (input.freshSuffix first))
    {m n : ℕ} {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) seed truth tapes m parent)
    (hc : Prefix (input.freshSuffix first) childC .uncapped childAccounting
      (referenceRule (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none) seed childTruth childTapes n child)
    (view : ReferenceSuffixView I first base.seen parent child) :
    referenceRule input available budget none seed parent.history =
      referenceSuffixActionLift I first (historyActions base.seen).length
        (referenceRule (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none seed child.history) := by
  have hbpos : 0 < 2 * risk := by linarith [hbase.valid.1]
  have hbsmall : 2 * risk ≤ 1 / 2 := by linarith [hbase.valid.2]
  have hparent := referenceRule_eq_candidate_of_prefix input C hearly accounting available budget hbudget hsmall none seed truth tapes hp
  have hchild := referenceRule_eq_candidate_of_prefix (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) hbpos hbsmall none seed childTruth childTapes hc
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) hbpos hbsmall none seed childTruth childTapes hc
  rw [hparent, hchild, view.history]
  exact referenceSuffix_candidateAction input first available budget risk base hbase hparseBase child.history cache haligned.parsed

private theorem suffixTapeCast_val (E F : BinaryExperiment) (he : E = F) (tape : F.Tape) (k : ℕ) :
    ((Eq.mpr (congrArg (fun G : BinaryExperiment => G.Tape) he) tape) k).val = (tape k).val := by
  cases he
  rfl

theorem referenceSuffixWorld_letter (input : StatisticalInput I) (first : ℕ) (world : input.World)
    (stage : (I.freshSuffix first).Stage) (k : ℕ) :
    (worldTapes (input.freshSuffix first) (referenceSuffixWorld input first world) stage k).val =
      (worldTapes input world (I.freshStageLift first stage) k).val := by
  exact suffixTapeCast_val _ _ (input.freshSuffix_experiment first stage) (world (I.freshStageLift first stage)).2 k

/-- Counts needed by the next review are recovered from the two true
history queries; no ledger equality or finite expected cost is assumed. -/
theorem referenceSuffix_reviews_of_prefixes {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (childC : Contract (I.freshSuffix first)) (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (childTruth : (I.freshSuffix first).Stage → Bool) (childTapes : ReviewTapes (input.freshSuffix first))
    {m n : ℕ} {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes m parent)
    (hc : Prefix (input.freshSuffix first) childC .uncapped childAccounting childRule seed childTruth childTapes n child)
    (before : List (VisibleEvent I)) (view : ReferenceSuffixView I first before parent child)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage, historyObservations before (I.freshStageLift first stage) = [])
    (stage : (I.freshSuffix first).Stage) :
    parent.ledger.reviews (I.freshStageLift first stage) = child.ledger.reviews stage := by
  have hg := prefix_historyObservations_length input C .uncapped accounting rule seed truth tapes hp (I.freshStageLift first stage)
  have hl := prefix_historyObservations_length (input.freshSuffix first) childC .uncapped childAccounting childRule seed childTruth childTapes hc stage
  rw [view.history, historyObservations_referenceSuffixJoin I first before child.history stage (hbefore stage)] at hg
  exact hg.symm.trans hl

/-- Full pointwise returned-action run view, conditional only on the
ordinary initial view used by induction. The actual-entry theorem below
constructs that view from the original run. No a.s. termination is used. -/
theorem referenceSuffix_run_view {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (base : ReferenceReplayCache I) (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : referenceAvailableReplay input available budget base.seen = some base)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first)) (sample : Seed × input.World) (start : ℕ)
    (hstart : ReferenceSuffixView I first base.seen
      (run input C .uncapped accounting (referenceRule input available budget none) sample start)
      (initial ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2)))) :
    ∀ k : ℕ, ReferenceSuffixView I first base.seen
      (run input C .uncapped accounting (referenceRule input available budget none) sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting
        (referenceRule (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none)
        (sample.1, referenceSuffixWorld input first sample.2) k) := by
  let rule : PolicyRule I Seed := referenceRule input available budget none
  let childRule : PolicyRule (I.freshSuffix first) Seed :=
    referenceRule (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none
  let childSample : Seed × (input.freshSuffix first).World := (sample.1, referenceSuffixWorld input first sample.2)
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hearly accounting available budget none
  have hchildLegal := referenceRule_uncapped_legal (Seed := Seed) (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) none
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero, run] using hstart
  | succ k ih =>
    change ReferenceSuffixView I first base.seen (run input C .uncapped accounting rule sample (start + (k + 1)))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample (k + 1))
    by_cases hh : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = true
    · have hparentHalt : (run input C .uncapped accounting rule sample (start + k)).halted = true := ih.halted.trans hh
      rw [Nat.add_succ, run_succ_of_halted input C .uncapped accounting rule sample (start + k) hparentHalt,
        run_succ_of_halted (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k hh]
      exact ih
    · have hchildActive : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = false := Bool.eq_false_iff.mpr hh
      have hparentActive : (run input C .uncapped accounting rule sample (start + k)).halted = false := ih.halted.trans hchildActive
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
      obtain ⟨l, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
      have ha := referenceSuffix_rule_of_prefixes input first available budget risk hbudget hsmall base hbase hparseBase
        C hearly accounting childC hchildEarly childAccounting sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
        ((input.freshSuffix first).truthAt childSample.2) (worldTapes (input.freshSuffix first) childSample.2) hp hc ih
      obtain ⟨nextParent, hps⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) m _ hp hparentActive
      obtain ⟨nextChild, hcs⟩ := hchildLegal sample.1 ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) l _ hc hchildActive
      have hpsLift := hps
      rw [ha] at hpsLift
      have hcounts := referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) hp hc base.seen ih hbase.observations
      have htruths : ∀ stage, (run input C .uncapped accounting rule sample (start + k)).ledger.truth (I.freshStageLift first stage) =
          (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).ledger.truth stage := by
        intro stage
        calc
          _ = input.truthAt sample.2 (I.freshStageLift first stage) := congrFun (prefix_truth input C .uncapped accounting rule sample.1 _ _ hp) _
          _ = (input.freshSuffix first).truthAt childSample.2 stage := rfl
          _ = _ := (congrFun (prefix_truth (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc) stage).symm
      have hnext := referenceSuffix_step_view input first C childC hearly hchildEarly accounting childAccounting
        (worldTapes input sample.2) (worldTapes (input.freshSuffix first) childSample.2) base.seen ih hcounts htruths
        (fun stage index => (referenceSuffixWorld_letter input first sample.2 stage index).symm) hpsLift hcs
      rw [Nat.add_succ, run_succ_of_step input C .uncapped accounting rule sample (start + k) nextParent hparentActive hps,
        run_succ_of_step (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k nextChild hchildActive hcs]
      exact hnext

/-- Full actual entry-to-fresh-suffix run transport, on EVERY sample and
EVERY returned-action clock, including failure, abandonment and infinite
review paths. The source view is obtained from actual Prefix alignment. -/
theorem referenceEntry_run_view {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ (base : ReferenceReplayCache I) (risk : ℚ) (start : ℕ), base.seen = history ∧
      referenceAvailableEntryRisk input available budget history = some risk ∧
      ReferenceSuffixBase I stage.val budget risk base ∧
      (run input C .uncapped accounting (referenceRule input available budget none) sample start).cursor = stage.val ∧
      (∀ k < start, (run input C .uncapped accounting (referenceRule input available budget none) sample k).cursor ≠ stage.val) ∧
      (run input C .uncapped accounting (referenceRule input available budget none) sample start).history = history ∧
      ∀ k : ℕ, ReferenceSuffixView I stage.val history
        (run input C .uncapped accounting (referenceRule input available budget none) sample (start + k))
        (run (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix stage.val))
          (referenceRule (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
          (sample.1, referenceSuffixWorld input stage.val sample.2) k) := by
  obtain ⟨base, risk, hparse, hseen, hrisk, hbase⟩ := referenceEntry_suffixBase input C hearly accounting available budget
    hbudget hsmall sample stage history hentry
  obtain ⟨start, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (referenceRule input available budget none) stage sample history).mp hentry
  have hparseBase : referenceAvailableReplay input available budget base.seen = some base := by rw [hseen]; exact hparse
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hearly accounting available budget none
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none) hlegal sample start
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hparsed : referenceAvailableReplay input available budget history = some cache := by rw [← hhistory]; exact haligned.parsed
  have heq : cache = base := Option.some.inj (hparsed.symm.trans hparse)
  subst cache
  have hhalt : (run input C .uncapped accounting (referenceRule input available budget none) sample start).halted = false :=
    haligned.halted.symm.trans hbase.active
  have hclock : (run input C .uncapped accounting (referenceRule input available budget none) sample start).clock =
      (historyActions base.seen).length := by
    rw [← prefix_historyActions_length input C .uncapped accounting (referenceRule input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp, hhistory, hseen]
  have hstart : ReferenceSuffixView I stage.val base.seen
      (run input C .uncapped accounting (referenceRule input available budget none) sample start)
      (initial ((input.freshSuffix stage.val).truthAt (referenceSuffixWorld input stage.val sample.2))) := by
    constructor
    · simpa only [initial, referenceSuffixHistoryJoin, referenceSuffixHistoryLift, List.map_nil, List.append_nil] using hhistory.trans hseen.symm
    · simpa only [initial, Nat.add_zero] using hcursor
    · simpa only [initial, Nat.add_zero] using hclock
    · exact hhalt
  refine ⟨base, risk, start, hseen, hrisk, hbase, hcursor, hbefore, hhistory, ?_⟩
  intro k
  simpa only [hseen] using referenceSuffix_run_view input stage.val available budget risk hbudget hsmall base hbase hparseBase
    C hearly accounting (currentRelaxedContract (I.freshSuffix stage.val)) rfl (zeroNormalAccounting (I.freshSuffix stage.val)) sample start hstart k

theorem sum_referenceSuffix_stages (I : Instance) (first : ℕ) (f : I.Stage → ℝ≥0∞) :
    (∑ stage : I.Stage, if first ≤ stage.val then f stage else 0) =
      ∑ stage : (I.freshSuffix first).Stage, f (I.freshStageLift first stage) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun stage _ => I.freshStageLift first stage)
  · intro stage _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change first ≤ first + stage.val; omega⟩
  · intro left _ right _ he
    exact freshStageLift_injective I first he
  · intro stage hs
    have hb := (Finset.mem_filter.mp hs).2
    let child : (I.freshSuffix first).Stage := ⟨stage.val - first, by
      have hstage := stage.isLt
      change stage.val - first < (I.compatibility.drop first).length
      rw [List.length_drop]
      omega⟩
    refine ⟨child, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp only [Instance.freshStageLift, child]
    omega
  · intro _ _
    rfl

/-- An all-clock public run view gives exactly the same one-stage paid
observation bill. Monotone sup shifting retains pre-entry payments and infinity. -/
theorem referenceSuffix_stageBill_of_run_view {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first)) (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage, historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k)) (stage : (I.freshSuffix first).Stage) :
    runStageObservationBill input C .uncapped accounting rule (I.freshStageLift first stage) sample =
      runStageObservationBill (input.freshSuffix first) childC .uncapped childAccounting childRule stage
        (sample.1, referenceSuffixWorld input first sample.2) := by
  let childSample := (sample.1, referenceSuffixWorld input first sample.2)
  have hcounts (k : ℕ) : (run input C .uncapped accounting rule sample (start + k)).ledger.reviews (I.freshStageLift first stage) =
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).ledger.reviews stage := by
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
    obtain ⟨_, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
    exact referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) ((input.freshSuffix first).truthAt childSample.2)
      (worldTapes (input.freshSuffix first) childSample.2) hp hc before (views k) hbefore stage
  have hfee : input.fees.observation (I.freshStageLift first stage) = (input.freshSuffix first).fees.observation stage :=
    congrArg BinaryExperiment.observationFee (input.freshSuffix_experiment first stage).symm
  let f : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (input.fees.observation (I.freshStageLift first stage) : ℝ) *
    ((run input C .uncapped accounting rule sample n).ledger.reviews (I.freshStageLift first stage) : ℝ≥0∞)
  have hmono : Monotone f := by
    intro a b hab
    exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C .uncapped accounting rule hlegal sample
      (I.freshStageLift first stage) hab)) _
  change (⨆ n, f n) = _
  rw [← hmono.iSup_nat_add start]
  apply iSup_congr
  intro k
  change ENNReal.ofReal (input.fees.observation (I.freshStageLift first stage) : ℝ) *
      ((run input C .uncapped accounting rule sample (k + start)).ledger.reviews (I.freshStageLift first stage) : ℝ≥0∞) = _
  rw [Nat.add_comm k start, hcounts k, hfee]

/-- Full remaining observation bill identity, with no subtraction of two
infinite bills, successful-path conditioning or finite expectation premise. -/
theorem referenceSuffix_observationBill_of_run_view {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first)) (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage, historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k)) :
    runRemainingObservationBill input C .uncapped accounting rule first sample =
      runObservationBill (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) := by
  rw [runRemainingObservationBill, sum_referenceSuffix_stages,
    runObservationBill_eq_sum_stage (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal]
  apply Finset.sum_congr rfl
  intro stage _
  exact referenceSuffix_stageBill_of_run_view input first C accounting rule hlegal childC childAccounting childRule hchildLegal
    sample before start hbefore views stage

/-- The previously stated full B18 pathwise execution/observation target,
now proved from the original actual entry, with no added controller fields. -/
theorem referenceSuffixRunTransport (input : StatisticalInput I) (Seed : Type*) : ReferenceSuffixRunTransport input Seed := by
  intro C hcurrent accounting available budget hbudget hsmall sample stage history hentry
  obtain ⟨base, risk, start, hseen, hrisk, hbase, hcursor, hbefore, hhistory, views⟩ :=
    referenceEntry_run_view input C hcurrent.1 accounting available budget hbudget hsmall sample stage history hentry
  let childC := currentRelaxedContract (I.freshSuffix stage.val)
  let childAccounting := zeroNormalAccounting (I.freshSuffix stage.val)
  let childRule : PolicyRule (I.freshSuffix stage.val) Seed :=
    referenceRule (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none
  let childSample := (sample.1, referenceSuffixWorld input stage.val sample.2)
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hcurrent.1 accounting available budget none
  have hchildLegal := referenceRule_uncapped_legal (Seed := Seed) (input.freshSuffix stage.val) childC rfl childAccounting
    (available \ historyUsed (I := I) history) (2 * risk) none
  have hobs : ∀ target : (I.freshSuffix stage.val).Stage, historyObservations history (I.freshStageLift stage.val target) = [] := by
    simpa only [hseen] using hbase.observations
  refine ⟨risk, start, hrisk, hbase.valid, hcursor, hbefore, hhistory, ?_⟩
  refine ⟨?_, ?_⟩
  · intro k
    have hv := views k
    refine ⟨hv.history, hv.cursor, hv.clock, hv.halted, ?_⟩
    intro target
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none) hlegal sample (start + k)
    obtain ⟨_, _, hc⟩ := run_has_prefix (input.freshSuffix stage.val) childC .uncapped childAccounting childRule hchildLegal childSample k
    exact referenceSuffix_reviews_of_prefixes input stage.val C accounting (referenceRule input available budget none)
      childC childAccounting childRule sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      ((input.freshSuffix stage.val).truthAt childSample.2) (worldTapes (input.freshSuffix stage.val) childSample.2)
      hp hc history hv hobs target
  · exact referenceSuffix_observationBill_of_run_view input stage.val C accounting (referenceRule input available budget none) hlegal
      childC childAccounting childRule hchildLegal sample history start hobs views

theorem referenceSuffixWorld_eq_restrictFreshWorld (input : StatisticalInput I) (first : ℕ)
    (world : input.World) : referenceSuffixWorld input first world = input.restrictFreshWorld first world := by
  cases first with
  | zero =>
    funext stage
    have hi : I.freshStageLift 0 stage = stage := by apply Fin.ext; exact Nat.zero_add _
    have transport (left right : I.Stage) (h : left = right)
        (he : input.experiment right = input.experiment left) :
        ((world left).1, Eq.mpr (congrArg (fun E : BinaryExperiment => E.Tape) he) (world left).2) = world right := by
      subst right
      rfl
    exact transport _ _ hi (input.freshSuffix_experiment 0 stage)
  | succ first => rfl

/-- The exact entry-selected fresh reference cost, without choosing an
arbitrary completion of the old hidden state or subtracting past costs. -/
theorem referenceEntry_observationBill_eq_freshSuffix {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (risk : ℚ)
    (hrisk : referenceAvailableEntryRisk input available budget history = some risk)
    (sample : Seed × input.World)
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) stage.val sample =
      runObservationBill (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix stage.val))
        (referenceRule (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
        (sample.1, input.restrictFreshWorld stage.val sample.2) := by
  obtain ⟨r, _, hr, _, _, _, _, _, hbill⟩ :=
    referenceSuffixRunTransport input Seed C hcurrent accounting available budget hbudget hsmall sample stage history hentry
  have heq : r = risk := Option.some.inj (hr.symm.trans hrisk)
  subst r
  simpa only [referenceSuffixWorld_eq_restrictFreshWorld] using hbill

section EntryMass

variable {Seed : Type} [MeasurableSpace Seed]

/-- The complete fresh world is independent of the true first-entry history
and the private seed jointly. The factorization is proved from actual Steps. -/
theorem entrySeedHistory_independent_freshSuffix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage) :
    IndepFun (entrySeedHistory input C mode accounting policy.rule next)
      (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2)
        (input.seededWorldLaw ν) := by
  exact entryHistorySeedRecord_independent_freshSuffix input C mode accounting policy ν next

theorem entrySeedHistory_jointFreshSuffixLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedHistory input C mode accounting policy.rule next sample,
          input.restrictFreshWorld next.val sample.2)) =
      ((input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next)).prod
        (input.freshSuffix next.val).worldLaw := by
  have hind := entrySeedHistory_independent_freshSuffix input C mode accounting policy ν next
  have hm := measurable_entrySeedHistory input C mode accounting policy.rule policy.measurable_rule next
  have hf : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hf.aemeasurable, seededWorldLaw_freshSuffixWorld]

end EntryMass

/-- Exact genuine entry-atom/fresh-world product integration. No positive
entry mass, integrability, regular conditional law or success gate is assumed. -/
theorem lintegral_on_referenceEntry_freshSuffixFunction
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (f : (input.freshSuffix stage.val).World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      f (input.restrictFreshWorld stage.val sample.2) ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        ∫⁻ world, f world ∂(input.freshSuffix stage.val).worldLaw := by
  classical
  let policy := referenceIdealPolicy input C hearly accounting available budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let atom : Set (Unit × EntryHistory I) := {((), some history)}
  let weight : Unit × EntryHistory I → ℝ≥0∞ := atom.indicator (fun _ => 1)
  let joint := fun sample : Unit × input.World => (record sample, input.restrictFreshWorld stage.val sample.2)
  let g : (Unit × EntryHistory I) × (input.freshSuffix stage.val).World → ℝ≥0∞ := fun z => weight z.1 * f z.2
  have hr : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hj : Measurable joint := hr.prodMk ((input.measurable_restrictFreshWorld stage.val).comp measurable_snd)
  have hw : Measurable weight := measurable_const.indicator (measurableSet_singleton _)
  have hg : Measurable g := (hw.comp measurable_fst).mul (hf.comp measurable_snd)
  have hpoint : ∀ sample : Unit × input.World,
      (referenceEntryEvent input C accounting available budget stage history).indicator
        (fun x => f (input.restrictFreshWorld stage.val x.2)) sample = g (joint sample) := by
    intro sample
    cases hu : sample.1
    by_cases he : entryHistory input C .uncapped accounting policy.rule stage sample = some history
    · have hm : sample ∈ referenceEntryEvent input C accounting available budget stage history := he
      rw [Set.indicator_of_mem hm]
      have hrval : record sample = ((), some history) := by simp only [record, entrySeedHistory, hu, he]
      simp only [g, joint, weight, hrval, atom, Set.indicator_of_mem (Set.mem_singleton _), one_mul]
    · have hm : sample ∉ referenceEntryEvent input C accounting available budget stage history := he
      rw [Set.indicator_of_notMem hm]
      have hrval : record sample ∉ atom := by
        intro hh
        exact he (congrArg Prod.snd (Set.mem_singleton_iff.mp hh))
      simp only [g, joint, weight, Set.indicator_of_notMem hrval, zero_mul]
  have hmass : (μ.map record) atom = μ (referenceEntryEvent input C accounting available budget stage history) := by
    rw [Measure.map_apply hr (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and]
    rfl
  calc
    _ = ∫⁻ sample, g (joint sample) ∂μ := by
      rw [← lintegral_indicator (measurableSet_referenceEntryEvent input C accounting available budget stage history)]
      exact lintegral_congr hpoint
    _ = ∫⁻ z, g z ∂μ.map joint := (lintegral_map hg hj).symm
    _ = ∫⁻ z, g z ∂(μ.map record).prod (input.freshSuffix stage.val).worldLaw := by
      rw [entrySeedHistory_jointFreshSuffixLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (∫⁻ r, weight r ∂μ.map record) * ∫⁻ x, f x ∂(input.freshSuffix stage.val).worldLaw :=
      lintegral_prod_mul hw.aemeasurable hf.aemeasurable
    _ = _ := by
      rw [show (∫⁻ r, weight r ∂μ.map record) = (μ.map record) atom by
        exact (lintegral_indicator_const (measurableSet_singleton _) 1).trans (one_mul _)]
      rw [hmass]

/-- Exact expected continuation fee on an actual entry atom. This uses the
proved same-world native run identity and the genuine product law, not a
Markov/freshness assumption about the controller. It retains zero entry mass,
failed/abandoned paths and infinite observation bills. Global iterated-log
bounds and the bad-child uniform bound remain separate obligations. -/
theorem referenceRemainingObservationBill_on_entry_eq_freshSuffix
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (risk : ℚ)
    (hrisk : referenceAvailableEntryRisk input available budget history = some risk) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        expectedObservationBill (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix stage.val))
          (referenceRule (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
          (Measure.dirac ()) := by
  let childInput := input.freshSuffix stage.val
  let childC := currentRelaxedContract (I.freshSuffix stage.val)
  let childAccounting := zeroNormalAccounting (I.freshSuffix stage.val)
  let childRule : PolicyRule (I.freshSuffix stage.val) Unit :=
    referenceRule childInput (available \ historyUsed (I := I) history) (2 * risk) none
  let f : childInput.World → ℝ≥0∞ :=
    fun world => runObservationBill childInput childC .uncapped childAccounting childRule ((), world)
  have hm : Measurable (runObservationBill childInput childC .uncapped childAccounting childRule) :=
    measurable_runObservationBill childInput childC .uncapped childAccounting childRule
      (measurable_referenceRule childInput (available \ historyUsed (I := I) history) (2 * risk) none)
  have hf : Measurable f := hm.comp (measurable_const.prodMk measurable_id)
  have hdirac : expectedObservationBill childInput childC .uncapped childAccounting childRule (Measure.dirac ()) =
      ∫⁻ world, f world ∂childInput.worldLaw := by
    change (∫⁻ sample, runObservationBill childInput childC .uncapped childAccounting childRule sample
      ∂(Measure.dirac ()).prod childInput.worldLaw) = _
    rw [lintegral_prod _ hm.aemeasurable]
    exact lintegral_dirac' _ (measurable_of_countable _)
  calc
    _ = ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
        f (input.restrictFreshWorld stage.val sample.2) ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_referenceEntryEvent input C accounting available budget stage history)
      intro sample hs
      exact referenceEntry_observationBill_eq_freshSuffix input C hcurrent accounting available budget hbudget hsmall
        stage history risk hrisk sample hs
    _ = input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        ∫⁻ world, f world ∂childInput.worldLaw :=
      lintegral_on_referenceEntry_freshSuffixFunction input C hcurrent.1 accounting available budget stage history f hf
    _ = _ := by rw [← hdirac]

end PaperProofs.Common.Native
