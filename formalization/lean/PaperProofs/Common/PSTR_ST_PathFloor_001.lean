module

public import PaperProofs.Common.ReferenceDecisionRealization

/-! B15c actual visible replay and Prefix budget/target floors.
For conservative rationalization R in [delta/2,delta], the proved floor
is R/C_N (hence delta/(2 C_N)), never the unsupported delta/C_N. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics

open PaperProofs.Statistics

variable {I : Instance}

theorem referenceAvailableReplay_risk_bounds (input : StatisticalInput I) (available : Finset I.Tool)
    (risk current : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input available risk history = some cache)
    (hcurrent : referenceReplayRisk risk cache = some current) :
    ReferenceBudgetValid current ∧ risk / (2 : ℚ) ^ (I.stageCount + 1) ≤ current := by
  have hs := referenceAvailableReplay_some_spec input available risk history cache hparse
  have hv : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  exact ⟨(referenceBudgetPath_valid_floor cache.events (risk / 2) current hv hcurrent).1,
    referenceBudgetPath_original_floor risk hs.1.1 hs.1.2 cache.events I.stageCount hs.2.2.2.1 current hcurrent⟩

theorem referenceAvailableCacheTarget_bounds (I : Instance) (available : Finset I.Tool)
    (risk target : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) (cache : ReferenceReplayCache I)
    (htarget : referenceAvailableCacheTarget I available risk cache = some target) :
    0 < target ∧ target ≤ 1 / 4 ∧ risk / referenceQuotaConstant I.stageCount ≤ target := by
  obtain ⟨kind, current, _, hpath, hv, hlen, ht⟩ := referenceAvailableCacheTarget_some_spec I available risk target cache htarget
  have hvalid := referenceBudgetTarget_valid_floor kind current target hv ht
  refine ⟨hvalid.1, hvalid.2.1, ?_⟩
  exact referenceBudgetPath_original_target_floor risk hrisk hsmall cache.events I.stageCount hlen current target hpath kind ht

theorem prefix_referenceRisk_native_floor {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit) seed truth tapes n s) :
    ∃ cache : ReferenceReplayCache I, ReferenceStateAligned input available budget cache s ∧
      ∀ current : ℚ, referenceReplayRisk budget cache = some current →
        ReferenceBudgetValid current ∧ budget / (2 : ℚ) ^ (I.stageCount + 1) ≤ current := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall
    limit seed truth tapes hp
  exact ⟨cache, haligned, fun current hcurrent =>
    referenceAvailableReplay_risk_bounds input available budget current s.history cache haligned.parsed hcurrent⟩

theorem prefix_referenceTarget_native_floor {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit) seed truth tapes n s) :
    ∃ cache : ReferenceReplayCache I, ReferenceStateAligned input available budget cache s ∧
      ∀ target : ℚ, referenceAvailableCacheTarget I available budget cache = some target →
        0 < target ∧ target ≤ 1 / 4 ∧ budget / referenceQuotaConstant I.stageCount ≤ target := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall
    limit seed truth tapes hp
  exact ⟨cache, haligned, fun target htarget =>
    referenceAvailableCacheTarget_bounds I available budget target hbudget hsmall cache htarget⟩

theorem referenceTarget_originalDelta_floor (I : Instance) (available : Finset I.Tool)
    (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (cache : ReferenceReplayCache I) (target : ℚ)
    (htarget : referenceAvailableCacheTarget I available budget cache = some target) :
    delta / (2 * (referenceQuotaConstant I.stageCount : ℝ)) ≤ (target : ℝ) := by
  have hf : (budget : ℝ) / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ) := by
    exact_mod_cast (referenceAvailableCacheTarget_bounds I available budget target choice.positive choice.small cache htarget).2.2
  have hC : (0 : ℝ) ≤ (referenceQuotaConstant I.stageCount : ℝ) := by
    simp only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    positivity
  calc
    _ = (delta / 2) / (referenceQuotaConstant I.stageCount : ℝ) := by ring
    _ ≤ (budget : ℝ) / (referenceQuotaConstant I.stageCount : ℝ) :=
      div_le_div_of_nonneg_right choice.factor_two hC
    _ ≤ _ := hf

end PaperProofs.Common.Native.PSTRStatistics
