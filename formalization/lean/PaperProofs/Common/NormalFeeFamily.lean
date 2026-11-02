module

public import PaperProofs.Common.NormalCharges
public import PaperProofs.Common.NativeSeed
public import PaperProofs.Common.ReferenceNativeRisk

/-!
One fixed normal-billing interface is evaluated on the public execution,
not chosen independently for each private-seed representation. Snapshots
exclude hidden ledger truths, future tape letters and private seed values.
This is a selected trace-billing realization. The manuscript's C0 bounds
alone do not imply that every permitted normal charge factors through this
trace; this module therefore does not close the general M11 fee interface.
Original success/constructed-run C0 bounds remain explicit assumptions.
The full total-cost infimum uses precisely Native.value's policies, laws
and risk constraint. Arbitrary seed universes are transported by the actual
proved same-run encoding, with no finiteness assumption on charges.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

abbrev NormalSnapshot (I : Instance) :=
  List (VisibleEvent I) × ℕ∞ × ℕ × ℕ × Bool

abbrev NormalTrace (I : Instance) := ℕ → NormalSnapshot I

def normalSnapshot {I : Instance} (state : State I) : NormalSnapshot I :=
  (state.history, state.ledger.normalCalls, state.cursor, state.clock, state.halted)

structure NormalBilling (I : Instance) where
  charge : NormalTrace I → ℝ≥0∞
  measurable_charge : Measurable charge

variable {I : Instance}

noncomputable def normalTrace {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) : NormalTrace I :=
  fun n => normalSnapshot (run input C mode accounting rule sample n)

theorem measurable_normalTrace {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (normalTrace input C mode accounting rule) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_of_countable normalSnapshot).comp (measurable_run input C mode accounting rule hm n)

noncomputable def NormalBilling.charges {Seed : Type*} [MeasurableSpace Seed] (billing : NormalBilling I)
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) : NormalCharges input Seed where
  normalCharge := fun sample => billing.charge (normalTrace input C mode accounting policy.rule sample)
  measurable_normalCharge := billing.measurable_charge.comp
    (measurable_normalTrace input C mode accounting policy.rule policy.measurable_rule)

theorem normalTrace_encoded_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (sample : Seed × input.World) :
    normalTrace input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) =
        normalTrace input C mode accounting policy.rule sample := by
  funext n
  exact congrArg normalSnapshot (run_encoded_eq input C mode accounting policy sample n)

theorem normalTrace_eq_of_run_eq {Seed Seed' : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode mode' : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (rule' : PolicyRule I Seed')
    (sample : Seed × input.World) (sample' : Seed' × input.World)
    (h : ∀ n, run input C mode accounting rule sample n = run input C mode' accounting rule' sample' n) :
    normalTrace input C mode accounting rule sample = normalTrace input C mode' accounting rule' sample' := by
  funext n
  exact congrArg normalSnapshot (h n)

/-- The original successful-run C0 lower assumption, uniformly on the
same comparison class as Native.value. Larger universes are covered below. -/
def NormalBilling.SuccessLower (billing : NormalBilling I) (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I) (C0 : ℝ≥0∞) : Prop :=
  ∀ (Seed : Type) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ policy : Policy input C mode accounting Seed,
      SuccessfulNormalChargeLower input C mode accounting policy (billing.charges input C mode accounting policy) C0

theorem NormalBilling.successLower_any_seed {Seed : Type*} [MeasurableSpace Seed]
    (billing : NormalBilling I) (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (C0 : ℝ≥0∞)
    (hlower : billing.SuccessLower input C mode accounting C0)
    (policy : Policy input C mode accounting Seed) :
    SuccessfulNormalChargeLower input C mode accounting policy (billing.charges input C mode accounting policy) C0 := by
  intro sample hs
  have h := hlower _ _ (strategyPolicy input C mode accounting)
    (encodeSeed input C mode accounting policy sample.1, sample.2)
    ((runSuccess_encoded_iff input C mode accounting policy sample).mpr hs)
  change C0 ≤ billing.charge (normalTrace input C mode accounting policy.rule sample)
  change C0 ≤ billing.charge (normalTrace input C mode accounting (strategyPolicy input C mode accounting).rule
    (encodeSeed input C mode accounting policy sample.1, sample.2)) at h
  rwa [normalTrace_encoded_eq] at h

noncomputable def NormalBilling.totalValue (billing : NormalBilling I) (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I) (delta : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : {p : Policy input C mode accounting Seed // risk input C mode accounting p.rule ν ≤ delta},
        totalExpectedBill input C mode accounting policy.val
          (billing.charges input C mode accounting policy.val) ν

theorem NormalBilling.totalExpectedBill_encoded_eq {Seed : Type*} [MeasurableSpace Seed]
    (billing : NormalBilling I) (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) :
    totalExpectedBill input C mode accounting (strategyPolicy input C mode accounting)
      (billing.charges input C mode accounting (strategyPolicy input C mode accounting))
      (encodedSeedLaw input C mode accounting policy ν) =
    totalExpectedBill input C mode accounting policy (billing.charges input C mode accounting policy) ν := by
  have hm : Measurable (fun sample : Seed × input.World =>
      (encodeSeed input C mode accounting policy sample.1, sample.2)) :=
    ((measurable_encodeSeed input C mode accounting policy).comp measurable_fst).prodMk measurable_snd
  unfold totalExpectedBill
  rw [seededWorldLaw_encoded input C mode accounting policy ν,
    lintegral_map (measurable_totalRunBill input C mode accounting _ _) hm]
  apply lintegral_congr
  intro sample
  change runActualBill input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) +
      billing.charge (normalTrace input C mode accounting (strategyPolicy input C mode accounting).rule
        (encodeSeed input C mode accounting policy sample.1, sample.2)) = _
  rw [runActualBill_encoded_eq, normalTrace_encoded_eq]
  rfl

theorem NormalBilling.totalValue_le_policy (billing : NormalBilling I) (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I) (delta : ℝ≥0∞)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy input C mode accounting Seed) (hsafe : risk input C mode accounting policy.rule ν ≤ delta) :
    billing.totalValue input C mode accounting delta ≤
      totalExpectedBill input C mode accounting policy (billing.charges input C mode accounting policy) ν := by
  exact iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le ⟨policy, hsafe⟩ le_rfl))))

theorem NormalBilling.totalValue_le_policy_any_seed {Seed : Type*} [MeasurableSpace Seed]
    (billing : NormalBilling I) (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (delta : ℝ≥0∞)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (policy : Policy input C mode accounting Seed)
    (hsafe : risk input C mode accounting policy.rule ν ≤ delta) :
    billing.totalValue input C mode accounting delta ≤
      totalExpectedBill input C mode accounting policy (billing.charges input C mode accounting policy) ν := by
  rw [← billing.totalExpectedBill_encoded_eq input C mode accounting policy ν]
  apply billing.totalValue_le_policy
  rw [risk_encoded_eq]
  exact hsafe

theorem NormalBilling.totalValue_lower (billing : NormalBilling I) (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I) (delta C0 : ℝ≥0∞)
    (hlower : billing.SuccessLower input C mode accounting C0) :
    value input C mode accounting delta + (1 - delta) * C0 ≤
      billing.totalValue input C mode accounting delta := by
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact (add_le_add (value_le_policy input C mode accounting delta ν policy.val policy.property) le_rfl).trans
    (totalExpectedBill_lower_of_safe input C mode accounting policy.val _ ν delta C0 policy.property
      (hlower Seed m policy.val))

theorem NormalBilling.totalValue_upper_of_constructed {Seed : Type*} [MeasurableSpace Seed]
    (billing : NormalBilling I) (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (delta C0 : ℝ≥0∞)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (policy : Policy input C mode accounting Seed)
    (hsafe : risk input C mode accounting policy.rule ν ≤ delta)
    (hcharge : ConstructedNormalChargeUpper input (billing.charges input C mode accounting policy) C0) :
    billing.totalValue input C mode accounting delta ≤ expectedBill input C mode accounting policy.rule ν + C0 :=
  (billing.totalValue_le_policy_any_seed input C mode accounting delta ν policy hsafe).trans
    (totalExpectedBill_upper_of_constructed input C mode accounting policy _ ν C0 hcharge)

/-- Full native total-value upper from the actual original-cap controller,
under the source's normal-fee upper on that fixed bounded execution. -/
theorem NormalBilling.totalNativeValue_le_referenceIdeal_add
    (billing : NormalBilling I) (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent)
    (C0 : ℝ≥0∞)
    (hcharge : ConstructedNormalChargeUpper input
      (billing.charges input C .uncapped accounting
        (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent)) C0) :
    billing.totalValue input C .native accounting (ENNReal.ofReal delta) ≤
      expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) + C0 := by
  obtain ⟨policy, hrule, hsafe, hbill⟩ := referenceNative_policy input C hcurrent accounting
    delta hd hsmall exponent budget choice qualification
  have hnormal : ConstructedNormalChargeUpper input (billing.charges input C .native accounting policy) C0 := by
    intro sample
    have htrace : normalTrace input C .native accounting policy.rule sample =
        normalTrace input C .uncapped accounting
          (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule sample := by
      apply normalTrace_eq_of_run_eq
      intro n
      rw [← run_uncapped_eq_native input C accounting policy.rule policy.legal sample n, hrule]
    change billing.charge (normalTrace input C .native accounting policy.rule sample) ≤ C0
    rw [htrace]
    exact hcharge sample
  exact (billing.totalValue_upper_of_constructed input C .native accounting (ENNReal.ofReal delta) C0
    (Measure.dirac ()) policy hsafe hnormal).trans (add_le_add hbill le_rfl)

end PaperProofs.Common.Native
