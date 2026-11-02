module

public import Common.PSTR_ST_SelectorAlignment_019
public import PaperProofs.Common.ReferenceSuffixRun

/-! Complete accepted-parser and candidate-action transport for a fixed ambient
selector. Every child inherits stage lifting and the old used-tool set; there
is no freshly rebuilt table or generic-picker run equality. Pure history,
serial, budget and target algebra is reused from the original suffix module. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Statistics

variable {I : Instance}

theorem selectorSuffixCacheJoin_step_observation (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (symbol : ℕ) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.observation stage symbol)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.observation stage symbol)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have htarget := referenceSuffixCacheJoin_target I first available budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_testing I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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

theorem selectorSuffixCacheJoin_step_write (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (bit : Bool) (serial : ℕ) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.wrote stage bit serial)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.wrote stage bit serial)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hkind := referenceSuffixCacheJoin_kind I first available budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase : (referenceSuffixCacheJoin I first base cache).phase = .testing ↔ cache.phase = .testing :=
    referenceSuffixPhaseLift_testing I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  have ha : (historyActions (referenceSuffixCacheJoin I first base cache).seen).length =
      (historyActions base.seen).length + (historyActions cache.seen).length := historyActions_referenceSuffixJoin_length I first base.seen cache.seen
  unfold step
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

theorem selectorSuffixCacheJoin_step_report (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) (truth : Bool) (serial : ℕ) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.report stage truth serial)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
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
  unfold step
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

theorem selectorSuffixCacheJoin_step_advance (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (stage : (I.freshSuffix first).Stage) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.advanced stage)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.advanced stage)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_reported I first cache.phase
  have hexecuted : (∃ tool : I.Tool, referenceSuffixPhaseLift I first cache.phase = .executed tool) ↔
      ∃ tool : (I.freshSuffix first).Tool, cache.phase = .executed tool := by
    cases cache.phase <;> simp [referenceSuffixPhaseLift]
    exact ⟨_, rfl⟩
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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

theorem selectorSuffixCacheJoin_step_execute (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (handle : MismatchHandle (I.freshSuffix first)) (tool : I.Tool) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.executed handle tool)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.executed handle tool)).map (referenceSuffixCacheJoin I first base) := by
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_allocated I first cache.phase tool
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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

section AllocationTransport

theorem selectorSuffixCacheJoin_step_allocate (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (handle : MismatchHandle (I.freshSuffix first)) (tool : I.Tool) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length (.committed handle tool)) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache (.committed handle tool)).map (referenceSuffixCacheJoin I first base) := by
  classical
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hrisk := referenceSuffixCacheJoin_risk I first budget risk base cache hbase
  have hphase := referenceSuffixPhaseLift_reported I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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
        have hpick : choose (I.freshStageLift first current)
            (historyUsed (referenceSuffixCacheJoin I first base cache).entryHistory) =
            restrict I choose first (historyUsed base.seen) current (historyUsed cache.entryHistory) := by
          rw [hentryUsed]
          rfl
        have hcondition :
            ((referenceSuffixCacheJoin I first base cache).phase = .reported ∧ referenceReplayMismatch cache current handle = true ∧
              tool ∈ I.eligible (I.freshStageLift first current) ∧
              tool ∉ historyUsed (referenceSuffixCacheJoin I first base cache).seen ∧
              tool ∈ available ∧ choose (I.freshStageLift first current)
                (historyUsed (referenceSuffixCacheJoin I first base cache).entryHistory) = some tool) ↔
            (cache.phase = .reported ∧ referenceReplayMismatch cache current handle = true ∧
              tool ∈ (I.freshSuffix first).eligible current ∧ tool ∉ historyUsed cache.seen ∧
              tool ∈ available \ historyUsed (I := I) base.seen ∧ restrict I choose first (historyUsed base.seen) current (historyUsed cache.entryHistory) = some tool) := by
          constructor
          · rintro ⟨hph, hm, he, hu, ha, selected⟩
            have he' : tool ∈ (I.freshSuffix first).eligible current := by
              rw [I.freshSuffix_eligible]
              exact he
            have hu' : tool ∉ historyUsed base.seen ∪ historyUsed (I := I.freshSuffix first) cache.seen := by
              rw [← hused]
              exact hu
            refine ⟨hphase.mp hph, hm, he', ?_, ?_, hpick.symm.trans selected⟩
            · intro ht
              exact hu' (Finset.mem_union_right _ ht)
            · exact Finset.mem_sdiff.mpr ⟨ha, fun ht => hu' (Finset.mem_union_left _ ht)⟩
          · rintro ⟨hph, hm, he, hu, ha, selected⟩
            have he' : tool ∈ I.eligible (I.freshStageLift first current) := by
              rw [I.freshSuffix_eligible] at he
              exact he
            refine ⟨hphase.mpr hph, hm, he', ?_, (Finset.mem_sdiff.mp ha).1, hpick.trans selected⟩
            intro ht
            rw [hused] at ht
            rcases Finset.mem_union.mp ht with hold | hnew
            · exact (Finset.mem_sdiff.mp ha).2 hold
            · exact hu hnew
        rw [if_congr hcondition rfl rfl]
        split_ifs with hg hc
        · simp only [Option.map_some, referenceSuffixCacheJoin, referenceSuffixHistoryJoin, referenceSuffixHistoryLift,
            List.map_append, List.map_cons, List.map_nil, List.append_assoc, referenceSuffixPhaseLift, hhcache,
            referenceSuffixEventLift]
        · exact False.elim (hc hg)
        · rename_i hc
          exact False.elim (hg hc)
        · rfl

end AllocationTransport

theorem selectorSuffixCacheJoin_step_stop (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache) .stopped =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache .stopped).map (referenceSuffixCacheJoin I first base) := by
  have hphase := referenceSuffixPhaseLift_testing I first cache.phase
  have hc : historyCursor (referenceSuffixCacheJoin I first base cache).seen = I.stageCount ↔
      historyCursor cache.seen = (I.freshSuffix first).stageCount := by
    change historyCursor (referenceSuffixHistoryJoin I first base.seen cache.seen) = I.stageCount ↔ _
    rw [historyCursor_referenceSuffixJoin, hbase.cursor, I.freshSuffix_stageCount]
    have hb := hbase.bound
    omega
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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

theorem selectorSuffixCacheJoin_step_abandon (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first)) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache) .abandoned =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)
        cache .abandoned).map (referenceSuffixCacheJoin I first base) := by
  have hphase := referenceSuffixPhaseLift_written I first cache.phase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  unfold step
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
theorem selectorSuffixCacheJoin_step (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (cache : ReferenceReplayCache (I.freshSuffix first))
    (hbase : ReferenceSuffixBase I first budget risk base) (event : VisibleEvent (I.freshSuffix first)) :
    step choose input available budget (referenceSuffixCacheJoin I first base cache)
      (referenceSuffixEventLift I first (historyActions base.seen).length event) =
      (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache event).map
        (referenceSuffixCacheJoin I first base) := by
  cases event with
  | observation stage symbol => exact selectorSuffixCacheJoin_step_observation choose input first available budget risk base cache hbase stage symbol
  | wrote stage bit serial => exact selectorSuffixCacheJoin_step_write choose input first available budget risk base cache hbase stage bit serial
  | report stage truth serial => exact selectorSuffixCacheJoin_step_report choose input first available budget risk base cache hbase stage truth serial
  | committed handle tool => exact selectorSuffixCacheJoin_step_allocate choose input first available budget risk base cache hbase handle tool
  | executed handle tool => exact selectorSuffixCacheJoin_step_execute choose input first available budget risk base cache hbase handle tool
  | advanced stage => exact selectorSuffixCacheJoin_step_advance choose input first available budget risk base cache hbase stage
  | stopped => exact selectorSuffixCacheJoin_step_stop choose input first available budget risk base cache hbase
  | abandoned => exact selectorSuffixCacheJoin_step_abandon choose input first available budget risk base cache

theorem selectorSuffixCacheJoin_fold (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first)) :
    (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
        (step choose input available budget) (referenceSuffixCacheJoin I first base cache) =
      (history.foldlM (step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk)) cache).map
        (referenceSuffixCacheJoin I first base) := by
  induction history generalizing cache with
  | nil => rfl
  | cons event rest ih =>
    simp only [referenceSuffixHistoryLift, List.map_cons, List.foldlM_cons]
    rw [selectorSuffixCacheJoin_step choose input first available budget risk base cache hbase event]
    cases hs : step (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) cache event with
    | none => rfl
    | some next =>
      simp only [Option.map_some]
      exact ih next

/-- The entire accepted suffix grammar, including reports, repairs and
terminal/failure responses, is accepted after the old actual visible entry.
This is a full parser transport, not merely equality of the first action. -/
theorem selectorSuffix_replay_join (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : replay choose input available budget base.seen = some base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hparse : replay (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) history = some cache) :
    replay choose input available budget (referenceSuffixHistoryJoin I first base.seen history) =
      some (referenceSuffixCacheJoin I first base cache) := by
  have hb := replay_some_spec choose input available budget base.seen base hparseBase
  have hf := replay_some_spec (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen)
    (2 * risk) history cache hparse
  have hfold : (referenceSuffixHistoryJoin I first base.seen history).foldlM
      (step choose input available budget) (referenceReplayInitial I) = some (referenceSuffixCacheJoin I first base cache) := by
    rw [referenceSuffixHistoryJoin, List.foldlM_append, hb.2.1]
    change (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
      (step choose input available budget) base = _
    calc
      _ = (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
          (step choose input available budget)
          (referenceSuffixCacheJoin I first base (referenceReplayInitial (I.freshSuffix first))) :=
        congrArg (fun start => (referenceSuffixHistoryLift I first (historyActions base.seen).length history).foldlM
          (step choose input available budget) start) (referenceSuffixCacheJoin_initial I first budget risk base hbase).symm
      _ = _ := (selectorSuffixCacheJoin_fold choose input first available budget risk base hbase history
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
  simp only [replay, hb.1]
  rw [hfold]
  exact ite_eq_left hfinal

theorem selectorSuffix_candidateAction (choose : Selector I) (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (budget risk : ℚ) (base : ReferenceReplayCache I)
    (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : replay choose input available budget base.seen = some base)
    (history : List (VisibleEvent (I.freshSuffix first))) (cache : ReferenceReplayCache (I.freshSuffix first))
    (hparse : replay (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) history = some cache) :
    candidate choose input available budget none (referenceSuffixHistoryJoin I first base.seen history) =
      referenceSuffixActionLift I first (historyActions base.seen).length
        (candidate (restrict I choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none history) := by
  have hg := selectorSuffix_replay_join choose input first available budget risk base hbase hparseBase history cache hparse
  have hstage := referenceSuffixCacheJoin_stage I first budget risk base cache hbase
  have hh : (referenceSuffixCacheJoin I first base cache).halted = cache.halted := rfl
  simp only [candidate, hg, hparse, hh]
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
      have hpick : choose (I.freshStageLift first stage)
          (historyUsed (referenceSuffixCacheJoin I first base cache).entryHistory) =
          restrict I choose first (historyUsed base.seen) stage (historyUsed cache.entryHistory) := by
        change choose (I.freshStageLift first stage)
          (historyUsed (referenceSuffixHistoryJoin I first base.seen cache.entryHistory)) = _
        rw [historyUsed_referenceSuffixJoin]
        rfl
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
            cases restrict I choose first (historyUsed base.seen) stage (historyUsed cache.entryHistory) <;> rfl


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector

