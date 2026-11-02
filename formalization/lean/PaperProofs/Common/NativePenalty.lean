module

public import PaperProofs.Common.NativeSeed
public import PaperProofs.Common.NativeCostBound
public import PaperProofs.Common.NativeContracts

/-!
One task-failure penalty on the genuine uncapped native policy class. The value
is a policy infimum, not a Bellman definition. Corrections are permitted under
the same contract, but their nonnegative monetary charges are omitted in this
relaxation. The lower bound retains all failed-path observation charges.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def penaltyObjective (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  expectedObservationBill input C mode accounting policy ν +
    penalty * risk input C mode accounting policy ν

noncomputable def penaltyValue (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (SmallSeed : Type), ⨅ (m : MeasurableSpace SmallSeed),
    letI : MeasurableSpace SmallSeed := m
    ⨅ (ν : Measure SmallSeed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : Policy input C .uncapped accounting SmallSeed,
        penaltyObjective input C .uncapped accounting policy.rule ν penalty

theorem penaltyValue_le_policy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) {SmallSeed : Type}
    [MeasurableSpace SmallSeed] (ν : Measure SmallSeed) [IsProbabilityMeasure ν]
    (policy : Policy input C .uncapped accounting SmallSeed) :
    penaltyValue input C accounting penalty ≤
      penaltyObjective input C .uncapped accounting policy.rule ν penalty := by
  exact iInf_le_of_le SmallSeed (iInf_le_of_le ‹MeasurableSpace SmallSeed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le policy le_rfl))))

theorem runObservationBill_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (sample : Seed × input.World) :
    runObservationBill input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) =
        runObservationBill input C mode accounting policy.rule sample := by
  simp only [runObservationBill, run_encoded_eq]

theorem expectedObservationBill_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodedSeedLaw input C mode accounting policy ν) =
        expectedObservationBill input C mode accounting policy.rule ν := by
  unfold expectedObservationBill
  have hm : Measurable (fun sample : Seed × input.World =>
      (encodeSeed input C mode accounting policy sample.1, sample.2)) :=
    ((measurable_encodeSeed input C mode accounting policy).comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_encoded input C mode accounting policy ν,
    lintegral_map (measurable_runObservationBill input C mode accounting _
      (strategyPolicy input C mode accounting).measurable_rule) hm]
  exact lintegral_congr (runObservationBill_encoded_eq input C mode accounting policy)

theorem penaltyValue_le_policy_any_seed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞)
    (policy : Policy input C .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    penaltyValue input C accounting penalty ≤
      penaltyObjective input C .uncapped accounting policy.rule ν penalty := by
  have h := penaltyValue_le_policy input C accounting penalty
    (encodedSeedLaw input C .uncapped accounting policy ν)
    (strategyPolicy input C .uncapped accounting)
  simpa only [penaltyObjective, expectedObservationBill_encoded_eq, risk_encoded_eq] using h

def abandonPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (Seed : Type*) [MeasurableSpace Seed] :
    Policy input C mode accounting Seed where
  rule _ _ := .abandon
  measurable_rule := measurable_const
  legal := by
    intro _ _ _ _ s _ hactive
    exact ⟨stopState s true, .abandon s hactive⟩

theorem abandon_run_one (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (sample : Seed × input.World) :
    run input C mode accounting (abandonPolicy input C mode accounting Seed).rule sample 1 =
      stopState (initial (input.truthAt sample.2)) true := by
  exact run_succ_of_step input C mode accounting _ sample 0 _ rfl (.abandon _ rfl)

theorem abandon_runActualBill (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (sample : Seed × input.World) :
    runActualBill input C mode accounting (abandonPolicy input C mode accounting Seed).rule sample = 0 := by
  have hh : (run input C mode accounting (abandonPolicy input C mode accounting Seed).rule sample 1).halted =
      true := by rw [abandon_run_one]; rfl
  rw [runActualBill_of_halted input C mode accounting _ sample 1 hh, abandon_run_one,
    stop_actualBill, initial_actualBill]

theorem abandon_expectedObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting (abandonPolicy input C mode accounting Seed).rule ν = 0 := by
  have heq (sample : Seed × input.World) :
      runObservationBill input C mode accounting (abandonPolicy input C mode accounting Seed).rule sample = 0 :=
    le_antisymm ((runObservationBill_le_actual input C mode accounting _ sample).trans_eq
      (abandon_runActualBill input C mode accounting sample)) zero_le
  simp only [expectedObservationBill, heq, lintegral_zero]

theorem penaltyValue_le_penalty (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) :
    penaltyValue input C accounting penalty ≤ penalty := by
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := penaltyValue_le_policy input C accounting penalty ν
    (abandonPolicy input C .uncapped accounting Unit)
  rw [penaltyObjective, abandon_expectedObservationBill, zero_add] at h
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_right (show risk input C .uncapped accounting
      (abandonPolicy input C .uncapped accounting Unit).rule ν ≤ 1 from prob_le_one) penalty)

theorem expectedObservationBill_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .native accounting Seed)
    (ν : Measure Seed) :
    expectedObservationBill input C .uncapped accounting policy.rule ν =
      expectedObservationBill input C .native accounting policy.rule ν := by
  unfold expectedObservationBill runObservationBill
  simp_rw [run_uncapped_eq_native input C accounting policy.rule policy.legal]

theorem penaltyValue_le_nativePolicy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty δ : ℝ≥0∞)
    (hsafe : risk input C .native accounting policy.rule ν ≤ δ) :
    penaltyValue input C accounting penalty ≤
      expectedBill input C .native accounting policy.rule ν + penalty * δ := by
  have h := penaltyValue_le_policy_any_seed input C accounting penalty
    (policy.relax input C accounting) ν
  change penaltyValue input C accounting penalty ≤
    expectedObservationBill input C .uncapped accounting policy.rule ν +
      penalty * risk input C .uncapped accounting policy.rule ν at h
  rw [expectedObservationBill_uncapped_eq_native input C accounting policy ν,
    risk_uncapped_eq_native input C accounting policy.rule policy.legal ν] at h
  apply h.trans
  exact add_le_add (expectedObservationBill_le_actual input C .native accounting policy.rule ν)
    (mul_le_mul_right hsafe penalty)

theorem penaltyValue_le_nativePolicy_observation (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty δ : ℝ≥0∞)
    (hsafe : risk input C .native accounting policy.rule ν ≤ δ) :
    penaltyValue input C accounting penalty ≤
      expectedObservationBill input C .native accounting policy.rule ν + penalty * δ := by
  have h := penaltyValue_le_policy_any_seed input C accounting penalty
    (policy.relax input C accounting) ν
  change penaltyValue input C accounting penalty ≤
    expectedObservationBill input C .uncapped accounting policy.rule ν +
      penalty * risk input C .uncapped accounting policy.rule ν at h
  rw [expectedObservationBill_uncapped_eq_native input C accounting policy ν,
    risk_uncapped_eq_native input C accounting policy.rule policy.legal ν] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_right hsafe penalty))

theorem expectedObservationBill_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    expectedObservationBill input C.deferExecution mode accounting policy.rule ν =
      expectedObservationBill input C mode accounting policy.rule ν := by
  unfold expectedObservationBill runObservationBill
  simp_rw [run_deferred_eq_original input C mode accounting policy.rule policy.legal]

theorem deferredPenalty_le_nativePolicy_observation (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty δ : ℝ≥0∞)
    (hsafe : risk input C .native accounting policy.rule ν ≤ δ) :
    penaltyValue input C.deferExecution accounting penalty ≤
      expectedObservationBill input C .native accounting policy.rule ν + penalty * δ := by
  have hs : risk input C.deferExecution .native accounting
      (policy.deferExecution input C .native accounting).rule ν ≤ δ := by
    change risk input C.deferExecution .native accounting policy.rule ν ≤ δ
    rw [risk_deferred_eq_original input C .native accounting policy.rule policy.legal]
    exact hsafe
  have h := penaltyValue_le_nativePolicy_observation input C.deferExecution accounting
    (policy.deferExecution input C .native accounting) ν penalty δ hs
  change penaltyValue input C.deferExecution accounting penalty ≤
    expectedObservationBill input C.deferExecution .native accounting policy.rule ν + penalty * δ at h
  rwa [expectedObservationBill_deferred_eq_original input C .native accounting policy ν] at h

theorem penaltyValue_sub_le_nativeValue (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty δ : ℝ≥0∞) :
    penaltyValue input C accounting penalty - penalty * δ ≤ value input C .native accounting δ := by
  unfold value
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact tsub_le_iff_right.mpr
    (penaltyValue_le_nativePolicy input C accounting policy.val ν penalty δ policy.property)

theorem inverseRisk_penalty_lower (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    penaltyValue input C accounting δ⁻¹ - 1 ≤ value input C .native accounting δ := by
  apply (tsub_le_tsub_left (ENNReal.inv_mul_le_one δ) _).trans
  exact penaltyValue_sub_le_nativeValue input C accounting δ⁻¹ δ

theorem inverseRisk_deferredPenalty_lower (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    penaltyValue input C.deferExecution accounting δ⁻¹ - 1 ≤ value input C .native accounting δ :=
  (inverseRisk_penalty_lower input C.deferExecution accounting δ).trans
    (value_deferred_le_original input C .native accounting δ)

theorem inverseRisk_deferredPenalty_le_observation (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (δ : ℝ≥0∞)
    (hsafe : risk input C .native accounting policy.rule ν ≤ δ) :
    penaltyValue input C.deferExecution accounting δ⁻¹ - 1 ≤
      expectedObservationBill input C .native accounting policy.rule ν := by
  apply tsub_le_iff_right.mpr
  exact (deferredPenalty_le_nativePolicy_observation input C accounting policy ν δ⁻¹ δ hsafe).trans
    (add_le_add le_rfl (ENNReal.inv_mul_le_one δ))

end PaperProofs.Common.Native
