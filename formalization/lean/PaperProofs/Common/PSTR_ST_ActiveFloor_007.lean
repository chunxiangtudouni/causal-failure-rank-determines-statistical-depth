module

public import PaperProofs.Common.PSTR_ST_TableAlignment_003
public import PaperProofs.Common.ReferenceDecisionRealization

/-! B15c exact ORIGINAL delta/C_N floor. A genuine testing stage has not
yet appended its own report, so at most N-1 budget events have occurred.
This recovers the factor two used by conservative rationalization without
changing the original exponent, quotas, constant or target. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.ActiveFloor

open PaperProofs.Statistics PaperProofs.Structure.LaminarTree
open CompactPrice TableAlignment

variable {I : Instance}

theorem activeBudget_originalDelta_floor (delta : ℝ) (N exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice N delta exponent budget)
    (events : List ReferenceBudgetEvent) (hlen : events.length < N) (current : ℚ)
    (hpath : referenceBudgetPath (budget / 2) events = some current) :
    delta / (2 : ℝ) ^ (N + 1) ≤ (current : ℝ) := by
  have hN : 1 ≤ N := by omega
  have hn : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hbound : events.length ≤ N - 1 := by omega
  have hf : (budget : ℝ) / (2 : ℝ) ^ N ≤ (current : ℝ) := by
    simpa only [hn] using referenceBudgetPath_original_floor_real budget choice.positive choice.small
      events (N - 1) hbound current hpath
  calc
    _ = (delta / 2) / (2 : ℝ) ^ N := by rw [pow_succ]; ring
    _ ≤ (budget : ℝ) / (2 : ℝ) ^ N :=
      div_le_div_of_nonneg_right choice.factor_two (by positivity)
    _ ≤ _ := hf

theorem activeTarget_originalDelta_floor (delta : ℝ) (N exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice N delta exponent budget)
    (events : List ReferenceBudgetEvent) (hlen : events.length < N) (current target : ℚ)
    (hpath : referenceBudgetPath (budget / 2) events = some current)
    (hvalid : ReferenceBudgetValid current) (kind : ReferenceBudgetCase)
    (htarget : referenceBudgetTarget kind current = some target) :
    delta / (referenceQuotaConstant N : ℝ) ≤ (target : ℝ) := by
  have hf := activeBudget_originalDelta_floor delta N exponent budget choice events hlen current hpath
  have ht : (current : ℝ) / 6 ≤ (target : ℝ) := by
    exact_mod_cast (referenceBudgetTarget_valid_floor kind current target hvalid htarget).2.2
  calc
    _ = (delta / (2 : ℝ) ^ (N + 1)) / 6 := by
      simp only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
      ring
    _ ≤ (current : ℝ) / 6 := div_le_div_of_nonneg_right hf (by norm_num)
    _ ≤ _ := ht

theorem referenceTestingCache_originalDelta_floor (input : StatisticalInput I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (cache : ReferenceReplayCache I) (s : State I)
    (aligned : ReferenceStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    (∀ current : ℚ, referenceReplayRisk budget cache = some current →
      delta / (2 : ℝ) ^ (I.stageCount + 1) ≤ (current : ℝ)) ∧
    (∀ target : ℚ, referenceAvailableCacheTarget I available budget cache = some target →
      delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ)) := by
  obtain ⟨_, _, _, _, _, hlen⟩ := referenceStateAligned_testing_ready input available budget cache s
    aligned hphase stage hcursor
  constructor
  · intro current hcurrent
    exact activeBudget_originalDelta_floor delta I.stageCount exponent budget choice cache.events hlen current hcurrent
  · intro target ht
    obtain ⟨kind, current, _, hc, hv, _, hb⟩ := referenceAvailableCacheTarget_some_spec I available budget target cache ht
    exact activeTarget_originalDelta_floor delta I.stageCount exponent budget choice cache.events hlen current target hc hv kind hb

theorem tableTestingCache_originalDelta_floor (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (available : Finset I.Tool)
    (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (cache : ReferenceReplayCache I) (s : State I)
    (aligned : TableStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    (∀ current : ℚ, referenceReplayRisk budget cache = some current →
      delta / (2 : ℝ) ^ (I.stageCount + 1) ≤ (current : ℝ)) ∧
    (∀ target : ℚ, tableTarget I available budget cache = some target →
      delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ)) := by
  obtain ⟨_, _, _, _, _, hlen⟩ := tableStateAligned_testing_ready hlaminar input available budget cache s
    aligned hphase stage hcursor
  constructor
  · intro current hcurrent
    exact activeBudget_originalDelta_floor delta I.stageCount exponent budget choice cache.events hlen current hcurrent
  · intro target ht
    obtain ⟨kind, current, _, hc, hv, _, hb⟩ := tableTarget_some_spec I available budget target cache ht
    exact activeTarget_originalDelta_floor delta I.stageCount exponent budget choice cache.events hlen current target hc hv kind hb

/-- Every actual testing Prefix, before any threshold check, has the exact
original path/target floor. This includes immediate zero-review writes. -/
theorem prefix_referenceTesting_originalDelta_floor {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit) seed truth tapes n s) :
    ∃ cache, ReferenceStateAligned input available budget cache s ∧
      ∀ (_hphase : cache.phase = .testing) (stage : I.Stage) (_hcursor : s.cursor = stage.val),
        (∀ current : ℚ, referenceReplayRisk budget cache = some current →
          delta / (2 : ℝ) ^ (I.stageCount + 1) ≤ (current : ℝ)) ∧
        (∀ target : ℚ, referenceAvailableCacheTarget I available budget cache = some target →
          delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ)) := by
  obtain ⟨cache, aligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    choice.positive choice.small limit seed truth tapes hp
  exact ⟨cache, aligned, fun phase stage cursor => referenceTestingCache_originalDelta_floor input available
    delta exponent budget choice cache s aligned phase stage cursor⟩

theorem prefix_tableTesting_originalDelta_floor (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∃ cache, TableStateAligned input available budget cache s ∧
      ∀ (_hphase : cache.phase = .testing) (stage : I.Stage) (_hcursor : s.cursor = stage.val),
        (∀ current : ℚ, referenceReplayRisk budget cache = some current →
          delta / (2 : ℝ) ^ (I.stageCount + 1) ≤ (current : ℝ)) ∧
        (∀ target : ℚ, tableTarget I available budget cache = some target →
          delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ)) := by
  obtain ⟨cache, aligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    choice.positive choice.small limit seed truth tapes hp
  exact ⟨cache, aligned, fun phase stage cursor => tableTestingCache_originalDelta_floor input hlaminar available
    delta exponent budget choice cache s aligned phase stage cursor⟩

end PaperProofs.Common.Native.PSTRStatistics.ActiveFloor
