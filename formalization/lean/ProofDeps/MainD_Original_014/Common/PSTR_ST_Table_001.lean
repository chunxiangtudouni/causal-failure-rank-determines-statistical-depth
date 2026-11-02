module

public import PaperProofs.Common.CompactPriceClaims
public import Structure.PSTR_Callback_001

/-! L01 same-cache rank formula and budget bounds for the actual table parser.
Different maximizing tools are allowed, so no parser/run equality is used. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree
open CompactPrice

variable {I : Instance}

theorem tableKind_eq_of_callbackClaims (hcallback : CompactControllerClaims.CallbackClaims)
    (I : Instance) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (cache : ReferenceReplayCache I) :
    tableKind I available cache = referenceAvailableKind I available cache := by
  have hrank := (hcallback I.toolCount I.compatibility hlaminar).1
  have hstage := (hcallback I.toolCount I.compatibility hlaminar).2.1
  unfold tableKind referenceAvailableKind
  cases hs : referenceReplayStage I cache with
  | none => rfl
  | some stage =>
    change referenceCaseOfRanks (tableReply I available stage (historyUsed cache.entryHistory)).rank
      (tableReply I available stage (historyUsed cache.entryHistory)).bad =
      referenceAvailableRankCase I available stage (historyUsed cache.entryHistory)
    unfold referenceAvailableRankCase referenceRankCase
    rw [referenceRankAt_eq, referenceBadRank_eq]
    unfold tableReply
    rw [hrank, (hstage stage _).2.1]
    rfl

theorem callbackFormulaClaims_of_callbackClaims (hcallback : CompactControllerClaims.CallbackClaims) :
    CallbackFormulaClaims := by
  intro I hlaminar available cache risk
  have hkind := tableKind_eq_of_callbackClaims hcallback I hlaminar available cache
  refine ⟨hkind, ?_⟩
  unfold tableTarget referenceAvailableCacheTarget
  rw [hkind]

theorem callbackFormulaClaims : CallbackFormulaClaims :=
  callbackFormulaClaims_of_callbackClaims PSTRCallback.callbackClaims

theorem tableTarget_some_spec (I : Instance) (available : Finset I.Tool) (risk target : ℚ) (cache : ReferenceReplayCache I)
    (htarget : tableTarget I available risk cache = some target) :
    ∃ kind current, tableKind I available cache = some kind ∧
      referenceReplayRisk risk cache = some current ∧ ReferenceBudgetValid current ∧
      cache.events.length ≤ I.stageCount ∧ referenceBudgetTarget kind current = some target := by
  cases hblocked : cache.halted || decide (cache.phase ≠ .testing) with
  | true =>
    simp only [tableTarget, hblocked, ite_true] at htarget
    cases htarget
  | false =>
    simp only [tableTarget, hblocked, Bool.false_eq_true, ite_false] at htarget
    obtain ⟨kind, hkind, hrest⟩ := Option.bind_eq_some_iff.mp htarget
    obtain ⟨current, hcurrent, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    by_cases hv : 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount
    · simp only [hv] at hrest
      exact ⟨kind, current, hkind, hcurrent, ⟨hv.1, hv.2.1⟩, hv.2.2, hrest⟩
    · simp only [hv, ite_false] at hrest
      cases hrest

theorem tableTarget_bounds (I : Instance) (available : Finset I.Tool)
    (risk target : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) (cache : ReferenceReplayCache I)
    (htarget : tableTarget I available risk cache = some target) :
    0 < target ∧ target ≤ 1 / 4 ∧ risk / referenceQuotaConstant I.stageCount ≤ target := by
  obtain ⟨kind, current, _, hpath, hv, hlen, ht⟩ := tableTarget_some_spec I available risk target cache htarget
  have hvalid := referenceBudgetTarget_valid_floor kind current target hv ht
  refine ⟨hvalid.1, hvalid.2.1, ?_⟩
  exact referenceBudgetPath_original_target_floor risk hrisk hsmall cache.events I.stageCount hlen current target hpath kind ht

theorem tableReplay_some_spec (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : tableReplay input available risk history = some cache) :
    (0 < risk ∧ risk ≤ 1 / 2) ∧
      history.foldlM (tableStep input available risk) (referenceReplayInitial I) = some cache ∧
      cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history := by
  by_cases hr : 0 < risk ∧ risk ≤ 1 / 2
  · simp only [tableReplay, hr] at hparse
    obtain ⟨result, hfold, hlast⟩ := Option.bind_eq_some_iff.mp hparse
    by_cases hg : result.phase ≠ .written ∧ result.events.length ≤ I.stageCount ∧
        historyCursor result.seen ≤ I.stageCount ∧ result.seen = history
    · rw [ite_eq_left hg] at hlast
      have heq := Option.some.inj hlast
      subst result
      exact ⟨hr, hfold, hg⟩
    · rw [ite_eq_right hg] at hlast
      cases hlast
  · simp only [tableReplay, hr, ite_false] at hparse
    cases hparse

/-- The budget bound now applies to accepted histories of the actual table
parser. It does not identify those histories with generic-tie histories. -/
theorem tableReplay_risk_bounds (input : StatisticalInput I) (available : Finset I.Tool)
    (risk current : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : tableReplay input available risk history = some cache)
    (hcurrent : referenceReplayRisk risk cache = some current) :
    ReferenceBudgetValid current ∧ risk / (2 : ℚ) ^ (I.stageCount + 1) ≤ current := by
  have hs := tableReplay_some_spec input available risk history cache hparse
  have hv : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  exact ⟨(referenceBudgetPath_valid_floor cache.events (risk / 2) current hv hcurrent).1,
    referenceBudgetPath_original_floor risk hs.1.1 hs.1.2 cache.events I.stageCount hs.2.2.2.1 current hcurrent⟩

end PaperProofs.Common.Native.PSTRStatistics
