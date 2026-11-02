module

public import PaperProofs.Common.PSTR_ST_ActiveFloor_007
public import PaperProofs.Common.ReferenceEntryFlow

/-! Original B15c scalar interfaces, now instantiated at every genuine
reference stage entry. No phase/alignment/path-floor premise is supplied.
This includes immediate zero-review writes and zero-probability entries. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.ActiveFloor

open PaperProofs.Statistics

variable {I : Instance}

private theorem run_first_stage_active {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (sample : Seed × input.World) (stage : I.Stage) (n : ℕ)
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

private theorem actualEntry_testing_cache {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) :
    ∃ (state : State I) (cache : ReferenceReplayCache I),
      ReferenceStateAligned input available budget cache state ∧ cache.phase = .testing ∧
      state.cursor = stage.val ∧ referenceAvailableReplay input available budget history = some cache := by
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (referenceRule input available budget none) stage sample history).mp hentry
  have hlegal : LegalRule input C .uncapped accounting (referenceRule (Seed := Seed) input available budget none) :=
    referenceRule_uncapped_legal input C hearly accounting available budget none
  have ha := run_first_stage_active input C accounting (referenceRule input available budget none) hlegal sample stage n hcursor hbefore
  have hp := run_prefix_of_active input C .uncapped accounting (referenceRule input available budget none) hlegal sample n ha
  obtain ⟨cache, entry, aligned, origin⟩ := referenceEntryBudgetTrace_of_prefix input C hearly accounting available budget
    hbudget hsmall sample hp ha stage hcursor
  have hsnapshot : cache.entryHistory = history := Option.some.inj (origin.actual_entry.symm.trans hentry)
  have hparse : referenceAvailableReplay input available budget history = some cache := by
    rw [← hhistory]
    exact aligned.parsed
  have hparseEntry : referenceAvailableReplay input available budget history = some entry := by
    rw [← hsnapshot]
    exact origin.parsed_entry
  have heq : entry = cache := Option.some.inj (hparseEntry.symm.trans hparse)
  subst entry
  exact ⟨_, cache, aligned, origin.entry_testing, hcursor, hparse⟩

theorem referenceEntry_current_native_floor {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) :
    ∃ current : ℚ, referenceAvailableEntryRisk input available budget history = some current ∧
      ReferenceBudgetValid current ∧ delta / (2 : ℝ) ^ (I.stageCount + 1) ≤ (current : ℝ) := by
  obtain ⟨state, cache, aligned, phase, cursor, parsed⟩ := actualEntry_testing_cache input C hearly accounting
    available budget choice.positive choice.small sample stage history hentry
  obtain ⟨_, current, _, hrisk, hvalid, _⟩ := referenceStateAligned_testing_ready input available budget cache state
    aligned phase stage cursor
  refine ⟨current, ?_, hvalid, ?_⟩
  · simp only [referenceAvailableEntryRisk, parsed, Option.bind_eq_bind, Option.bind_some, hrisk]
  · exact (referenceTestingCache_originalDelta_floor input available delta exponent budget choice cache state
      aligned phase stage cursor).1 current hrisk

theorem referenceEntry_target_native_floor {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) (target : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some target) :
    delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (target : ℝ) := by
  obtain ⟨state, cache, aligned, phase, cursor, parsed⟩ := actualEntry_testing_cache input C hearly accounting
    available budget choice.positive choice.small sample stage history hentry
  have ht : referenceAvailableCacheTarget I available budget cache = some target := by
    simpa only [referenceAvailableEntryTarget, parsed, Option.bind_eq_bind, Option.bind_some] using htarget
  exact (referenceTestingCache_originalDelta_floor input available delta exponent budget choice cache state
    aligned phase stage cursor).2 target ht

/-- The ORIGINAL controllerTarget_native_floor is called with a path floor
proved from the genuine entry, for every original positive bad depth. -/
theorem referenceEntry_controllerTarget_native_floor {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) (j : ℕ) (hj : 1 ≤ j) :
    ∃ current : ℚ, referenceAvailableEntryRisk input available budget history = some current ∧
      delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ (controllerTarget current j : ℝ) := by
  obtain ⟨current, hrisk, valid, floor⟩ := referenceEntry_current_native_floor input C hearly accounting
    available delta exponent budget choice sample stage history hentry
  refine ⟨current, hrisk, ?_⟩
  simpa only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using
    controllerTarget_native_floor delta I.stageCount current valid.1 valid.2 floor j hj

theorem referenceEntry_noToolTarget_native_floor {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) :
    ∃ current : ℚ, referenceAvailableEntryRisk input available budget history = some current ∧
      delta / (referenceQuotaConstant I.stageCount : ℝ) ≤ ((current / 2 : ℚ) : ℝ) := by
  obtain ⟨current, hrisk, valid, floor⟩ := referenceEntry_current_native_floor input C hearly accounting
    available delta exponent budget choice sample stage history hentry
  refine ⟨current, hrisk, ?_⟩
  simpa only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using
    noToolTarget_native_floor delta I.stageCount current valid.1 floor

/-- At each genuine entry-selected target, the original delta and original
minimal exponent can now be used directly in the original quota theorem.
This is a local truth-conditional SPRT law; the global entry-conditioned
actual-overflow statement remains the separately proved original B19. -/
theorem referenceEntry_originalQuota_overflow {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (hsmall : delta ≤ 1 / 2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none)
      stage sample = some history) (target : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some target) (truth : Bool) :
    (input.experiment stage).conditionalLaw (MeasureTheory.Measure.dirac ()) truth {localSample |
      (referenceQuota input exponent stage : ℕ∞) <
        ((input.experiment stage).posteriorSPRT target).rule.stop localSample.1 localSample.2} ≤
      ENNReal.ofReal (delta / (2 * I.stageCount)) := by
  have valid := referenceAvailableEntryTarget_valid input available budget target history htarget
  have floor := referenceEntry_target_native_floor input C hearly accounting available delta exponent budget
    choice sample stage history hentry target htarget
  have hd : 0 < delta := (show 0 < (budget : ℝ) by exact_mod_cast choice.positive).trans_le choice.conservative
  have hN : 0 < I.stageCount := by
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  exact (input.experiment stage).rationalQuota_conditional_overflow_le target valid.1 valid.2
    delta hd hsmall I.stageCount hN exponent choice.original_exponent.2.1 floor truth

end PaperProofs.Common.Native.PSTRStatistics.ActiveFloor
