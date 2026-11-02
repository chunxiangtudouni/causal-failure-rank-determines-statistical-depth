module

public import PaperProofs.Common.ReferenceObservationCost
public import PaperProofs.Common.ReferenceSuffixRun

/-!
Global finite upper bounds for the actual unchanged ideal reference bill.
All costs stay in ENNReal.  In particular, no finite-cost, termination,
Markov, alignment, or successful-path premise is used below.

This is a coarse logarithmic bound, not the still-pending rank-sensitive
iterated-log leading term or the uniform positive-depth bad-child bound.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

/-- The original parser target has the original quota denominator, also for
an arbitrary initial available set.  This is a theorem, not a changed budget. -/
theorem referenceAvailableEntryTarget_original_floor
    (input : StatisticalInput I) (available : Finset I.Tool) (budget p : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (history : List (VisibleEvent I))
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    budget / referenceQuotaConstant I.stageCount ≤ p := by
  obtain ⟨cache, _, ht⟩ := Option.bind_eq_some_iff.mp htarget
  obtain ⟨kind, current, _, hpath, _, hlen, hb⟩ :=
    referenceAvailableCacheTarget_some_spec I available budget p cache ht
  exact referenceBudgetPath_original_target_floor budget hbudget hsmall cache.events
    I.stageCount hlen current p hpath kind hb

/-- A deterministic finite allowance for one actual stage.  It is only an
upper bound on the original tests, and does not alter those tests. -/
noncomputable def referenceGlobalStageObservationPrice (input : StatisticalInput I)
    (budget : ℚ) (stage : I.Stage) : ℝ≥0∞ :=
  ENNReal.ofReal ((input.experiment stage).coefficient *
    (Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) +
      (input.experiment stage).logIncrementBound true +
      2 * |Real.log ((input.experiment stage).priorReal true /
        (input.experiment stage).priorReal false)|))

theorem referenceEntryLocalObservationPrice_le_global
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    referenceEntryLocalObservationPrice input available budget stage history ≤
      referenceGlobalStageObservationPrice input budget stage := by
  cases ht : referenceAvailableEntryTarget input available budget history with
  | none => simp only [referenceEntryLocalObservationPrice, ht]; exact bot_le
  | some p =>
    let E := input.experiment stage
    have hp := referenceAvailableEntryTarget_valid input available budget p history ht
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.1
    have hpone : (p : ℝ) ≤ 1 := by
      exact_mod_cast hp.2.trans (by norm_num : (1 / 4 : ℚ) ≤ 1)
    have hlog : 0 ≤ Real.log (1 / (p : ℝ)) :=
      Real.log_nonneg ((le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hpone))
    have hB : 0 ≤ Real.log (1 / (p : ℝ)) + E.logIncrementBound true +
        2 * |Real.log (E.priorReal true / E.priorReal false)| := by
      have hK := E.logIncrementBound_nonneg true
      positivity
    have hb := E.bayesObservationCharge_le_drift_bound (Measure.dirac ()) (E.posteriorSPRT p)
      _ hB (E.posteriorSPRT_expectedObservationCharge_finite p
        (BinaryExperiment.posteriorThreshold_nonneg p hp.1 hp.2))
      (fun x => by simpa only [add_assoc] using E.posteriorSPRT_sharpObservationCharge p hp.1 hp.2 x)
    have hfloor : (budget : ℝ) / (referenceQuotaConstant I.stageCount : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast referenceAvailableEntryTarget_original_floor input available budget p hbudget hsmall history ht
    have hbudgetR : 0 < (budget : ℝ) := by exact_mod_cast hbudget
    have hC : (0 : ℝ) < (referenceQuotaConstant I.stageCount : ℝ) := by
      unfold referenceQuotaConstant
      positivity
    have hratio : 1 / (p : ℝ) ≤ (referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ) := by
      calc
        _ ≤ 1 / ((budget : ℝ) / (referenceQuotaConstant I.stageCount : ℝ)) :=
          one_div_le_one_div_of_le (div_pos hbudgetR hC) hfloor
        _ = _ := by field_simp
    have hlogle := Real.log_le_log (one_div_pos.mpr hpR) hratio
    simp only [referenceEntryLocalObservationPrice, ht]
    change E.bayesObservationCharge (Measure.dirac ()) (E.posteriorSPRT p) ≤ _
    exact hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (by linarith) E.coefficient_pos.le))

/-- Actual entry atoms are disjoint; their total unnormalized mass is at most
one, including histories of zero mass and histories that are never entered. -/
theorem tsum_referenceEntryEvent_mass_le_one
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    (∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
      (referenceEntryEvent input C accounting available budget stage history)) ≤ 1 := by
  have hmass := tsum_measure_le_measure_univ
    (μ := input.seededWorldLaw (Measure.dirac ()))
    (s := fun history : List (VisibleEvent I) =>
      referenceEntryEvent input C accounting available budget stage history)
    (fun history => (measurableSet_referenceEntryEvent input C accounting available budget stage history).nullMeasurableSet)
    (by
      intro history other hne
      change input.seededWorldLaw (Measure.dirac ())
        (referenceEntryEvent input C accounting available budget stage history ∩
          referenceEntryEvent input C accounting available budget stage other) = 0
      have hempty : referenceEntryEvent input C accounting available budget stage history ∩
          referenceEntryEvent input C accounting available budget stage other = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro sample hs
        exact hne (Option.some.inj (hs.1.symm.trans hs.2))
      rw [hempty, measure_empty])
  simpa only [measure_univ] using hmass

theorem referenceEntryPriceSum_le_global
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget)
    (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∑' history : List (VisibleEvent I),
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        referenceEntryLocalObservationPrice input available budget stage history) ≤
      referenceGlobalStageObservationPrice input budget stage := by
  calc
    _ ≤ ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
          referenceGlobalStageObservationPrice input budget stage := by
      apply ENNReal.tsum_le_tsum
      intro history
      exact mul_le_mul_right (referenceEntryLocalObservationPrice_le_global input available budget
        hbudget hsmall stage history) _
    _ = (∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
        (referenceEntryEvent input C accounting available budget stage history)) *
          referenceGlobalStageObservationPrice input budget stage := ENNReal.tsum_mul_right
    _ ≤ 1 * referenceGlobalStageObservationPrice input budget stage :=
      mul_le_mul' (tsum_referenceEntryEvent_mass_le_one input C accounting available budget stage) le_rfl
    _ = _ := one_mul _

theorem referenceExpectedObservationBill_le_global
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      ∑ stage, referenceGlobalStageObservationPrice input budget stage := by
  apply (referenceExpectedObservationBill_le_entry_prices input C hearly accounting available budget hbudget hsmall).trans
  apply Finset.sum_le_sum
  intro stage _
  exact referenceEntryPriceSum_le_global input C accounting available budget hbudget hsmall stage

theorem referenceExpectedBill_le_global_add_corrections
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      (∑ stage, referenceGlobalStageObservationPrice input budget stage) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  exact (expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting available budget) (Measure.dirac ())).trans
      (add_le_add (referenceExpectedObservationBill_le_global input C hearly accounting available budget hbudget hsmall) le_rfl)

theorem referenceExpectedObservationBill_ne_top
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (referenceExpectedObservationBill_le_global input C hearly accounting available budget hbudget hsmall)
  exact (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)).ne

theorem referenceExpectedBill_ne_top
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (referenceExpectedBill_le_global_add_corrections input C hearly accounting available budget hbudget hsmall)
  exact ENNReal.add_ne_top.mpr ⟨(ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)).ne,
    ENNReal.mul_ne_top (by finiteness) input.fees.maxCorrection_lt_top.ne⟩

/-- A never-entered native stage is never passed: actual cursor increments
are at most one. This uses only the native run, not eventual termination. -/
theorem run_cursor_lt_of_no_entry {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (stage : I.Stage)
    (hnone : entryHistory input C mode accounting rule stage sample = none) (n : ℕ) :
    (run input C mode accounting rule sample n).cursor < stage.val := by
  have hne (k : ℕ) : (run input C mode accounting rule sample k).cursor ≠ stage.val :=
    fun he => (entryHistory_none_iff input C mode accounting rule stage sample).mp hnone ⟨k, he⟩
  induction n with
  | zero =>
    have hh := hne 0
    change (0 : ℕ) ≠ stage.val at hh
    change (0 : ℕ) < stage.val
    omega
  | succ n ih =>
    have hb := run_cursor_step_bounds input C mode accounting rule hlegal sample n
    have hh := hne (n + 1)
    omega

/-- No observations in this or any later stage are charged on an unentered
path. Failed, abandoned and infinite runs are all included. -/
theorem runRemainingObservationBill_zero_of_no_entry {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (stage : I.Stage)
    (hnone : entryHistory input C mode accounting rule stage sample = none) :
    runRemainingObservationBill input C mode accounting rule stage.val sample = 0 := by
  classical
  unfold runRemainingObservationBill
  apply Finset.sum_eq_zero
  intro current _
  split_ifs with hcurrent
  · have hz (n : ℕ) : (run input C mode accounting rule sample n).ledger.reviews current = 0 :=
      (run_cursorInvariant input C mode accounting rule hlegal sample n).future_reviews current
        ((run_cursor_lt_of_no_entry input C mode accounting rule hlegal sample stage hnone n).trans_le hcurrent)
    unfold runStageObservationBill
    simp only [hz, ENat.toENNReal_zero, mul_zero, iSup_const]
  · rfl

/-- The child cost is the actual fresh suffix run at the original parsed
budget 2r. Malformed histories have zero weight and a zero selected cost. -/
noncomputable def referenceEntryFreshObservationCost (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) : ℝ≥0∞ :=
  match referenceAvailableEntryRisk input available budget history with
  | none => 0
  | some risk =>
    expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (referenceRule (input.freshSuffix stage.val)
        (available \ historyUsed (I := I) history) (2 * risk) none) (Measure.dirac ())

theorem referenceAvailableEntryRisk_valid
    (input : StatisticalInput I) (available : Finset I.Tool) (budget risk : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (history : List (VisibleEvent I))
    (hrisk : referenceAvailableEntryRisk input available budget history = some risk) :
    ReferenceBudgetValid risk := by
  obtain ⟨cache, _, hpath⟩ := Option.bind_eq_some_iff.mp hrisk
  exact (referenceBudgetPath_valid_floor cache.events (budget / 2) risk
    ⟨by linarith, by linarith⟩ hpath).1

theorem referenceEntryFreshObservationCost_ne_top
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    referenceEntryFreshObservationCost input available budget stage history ≠ ⊤ := by
  cases hrisk : referenceAvailableEntryRisk input available budget history with
  | none => simp only [referenceEntryFreshObservationCost, hrisk]; exact ENNReal.zero_ne_top
  | some risk =>
    have hv := referenceAvailableEntryRisk_valid input available budget risk hbudget hsmall history hrisk
    simp only [referenceEntryFreshObservationCost, hrisk]
    exact referenceExpectedObservationBill_ne_top (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) rfl
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (available \ historyUsed (I := I) history) (2 * risk) (by linarith [hv.1]) (by linarith [hv.2])

/-- The entire actual continuation, decomposed into true entry atoms and
actual fresh-run costs at the original parsed continuation budget.  The
equality remains in ENNReal and does not require any finite-cost premise. -/
theorem referenceRemainingObservationBill_eq_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (referenceRule input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
          referenceEntryFreshObservationCost input available budget stage history := by
  rw [lintegral_eq_tsum_referenceEntry input C accounting available budget stage _
    (measurable_runRemainingObservationBill input C .uncapped accounting _
      (measurable_referenceRule input available budget none) stage.val)
    (fun sample hs => runRemainingObservationBill_zero_of_no_entry input C .uncapped accounting _
      (referenceRule_uncapped_legal input C hcurrent.1 accounting available budget none) sample stage hs)]
  apply tsum_congr
  intro history
  cases hrisk : referenceAvailableEntryRisk input available budget history with
  | none =>
    have hE : referenceEntryEvent input C accounting available budget stage history = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hs
      obtain ⟨_, risk, _, hr, _⟩ := referenceEntryRisk_kind_target input C hcurrent.1 accounting available budget
        hbudget hsmall sample stage history hs
      rw [hrisk] at hr
      cases hr
    simp only [hE, Measure.restrict_empty, lintegral_zero_measure,
      referenceEntryFreshObservationCost, hrisk, measure_empty, mul_zero]
  | some risk =>
    simpa only [referenceEntryFreshObservationCost, hrisk] using
      referenceRemainingObservationBill_on_entry_eq_freshSuffix input C hcurrent accounting available budget
        hbudget hsmall stage history risk hrisk

/-- A true one-stage global observation recurrence.  The successor term is
the sum of actual next-entry masses times actual fresh child costs, with
each child's original 2r budget and remaining available tools. -/
theorem referenceRemainingObservationBill_step_eq_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage nextStage : I.Stage) (hnext : nextStage.val = stage.val + 1) :
    (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (referenceRule input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      (∫⁻ sample, runStageObservationBill input C .uncapped accounting
        (referenceRule input available budget none) stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) +
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget nextStage history) *
          referenceEntryFreshObservationCost input available budget nextStage history := by
  calc
    _ = (∫⁻ sample, runStageObservationBill input C .uncapped accounting
        (referenceRule input available budget none) stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) +
        ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (referenceRule input available budget none) (stage.val + 1) sample
            ∂input.seededWorldLaw (Measure.dirac ()) := by
      simp_rw [runRemainingObservationBill_step input C .uncapped accounting _ stage]
      exact lintegral_add_left (measurable_runStageObservationBill input C .uncapped accounting _
        (measurable_referenceRule input available budget none) stage) _
    _ = _ := by
      rw [← hnext, referenceRemainingObservationBill_eq_entryFreshCosts input C hcurrent accounting available budget
        hbudget hsmall nextStage]

theorem runRemainingObservationBill_le_observation {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (first : ℕ) (sample : Seed × input.World) :
    runRemainingObservationBill input C mode accounting rule first sample ≤
      runObservationBill input C mode accounting rule sample := by
  classical
  rw [runRemainingObservationBill, runObservationBill_eq_sum_stage input C mode accounting rule hlegal]
  apply Finset.sum_le_sum
  intro stage _
  split_ifs
  · exact le_rfl
  · exact bot_le

/-- Even the countable successor-cost sum is finite, proved from the real
run's finite global bill rather than by a summability assumption. -/
theorem referenceEntryFreshObservationCostSum_ne_top
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∑' history : List (VisibleEvent I),
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        referenceEntryFreshObservationCost input available budget stage history) ≠ ⊤ := by
  rw [← referenceRemainingObservationBill_eq_entryFreshCosts input C hcurrent accounting available budget hbudget hsmall stage]
  apply ne_top_of_le_ne_top
    (referenceExpectedObservationBill_ne_top input C hcurrent.1 accounting available budget hbudget hsmall)
  exact lintegral_mono (runRemainingObservationBill_le_observation input C .uncapped accounting _
    (referenceRule_uncapped_legal input C hcurrent.1 accounting available budget none) stage.val)

theorem referenceInitialStageObservationBill_le_localPrice
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first : I.Stage) (hfirst : first.val = 0) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting
      (referenceRule input available budget none) first sample ∂input.seededWorldLaw (Measure.dirac ())) ≤
      referenceEntryLocalObservationPrice input available budget first [] := by
  have hE : referenceEntryEvent input C accounting available budget first [] = Set.univ := by
    apply Set.eq_univ_of_forall
    intro sample
    exact entryHistory_stageZero input C .uncapped accounting _ first hfirst sample
  cases ht : referenceAvailableEntryTarget input available budget [] with
  | none =>
    have hz := referenceStageObservationBill_on_entry_none input C hearly accounting available budget
      hbudget hsmall first [] ht
    rw [hE, Measure.restrict_univ] at hz
    simp only [referenceEntryLocalObservationPrice, ht]
    exact hz.le
  | some p =>
    have hb := referenceStageObservationBill_on_entry_le input C hearly accounting available budget
      hbudget hsmall first [] p ht
    rw [hE, Measure.restrict_univ, measure_univ, one_mul] at hb
    simpa only [referenceEntryLocalObservationPrice, ht] using hb

/-- Original-budget global recursion from the initial state.  The local
price is the unchanged SPRT selected on the empty initial history. The
successor sum charges every actual branch, with no successful-path filter. -/
theorem referenceExpectedObservationBill_le_initial_add_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first next : I.Stage) (hfirst : first.val = 0) (hnext : next.val = 1) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget next history) *
          referenceEntryFreshObservationCost input available budget next history := by
  have hlegal := referenceRule_uncapped_legal (Seed := Unit) input C hcurrent.1 accounting available budget none
  have hzero (sample : Unit × input.World) :
      runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) first.val sample =
        runObservationBill input C .uncapped accounting (referenceRule input available budget none) sample := by
    rw [hfirst]
    simpa only [runRemainingObservationBill, Nat.zero_le, ite_true] using
      (runObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal sample).symm
  calc
    _ = ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
        (referenceRule input available budget none) first.val sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr (fun sample => (hzero sample).symm)
    _ = _ := referenceRemainingObservationBill_step_eq_entryFreshCosts input C hcurrent accounting available budget
      hbudget hsmall first next (by omega)
    _ ≤ _ := add_le_add (referenceInitialStageObservationBill_le_localPrice input C hcurrent.1 accounting available budget
      hbudget hsmall first hfirst) le_rfl

theorem referenceExpectedBill_le_initial_add_entryFreshCosts_add_corrections
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first next : I.Stage) (hfirst : first.val = 0) (hnext : next.val = 1) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        ∑' history : List (VisibleEvent I),
          input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget next history) *
            referenceEntryFreshObservationCost input available budget next history) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  exact (expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hcurrent.1 accounting available budget) (Measure.dirac ())).trans
      (add_le_add (referenceExpectedObservationBill_le_initial_add_entryFreshCosts input C hcurrent accounting available budget
        hbudget hsmall first next hfirst hnext) le_rfl)

end PaperProofs.Common.Native
