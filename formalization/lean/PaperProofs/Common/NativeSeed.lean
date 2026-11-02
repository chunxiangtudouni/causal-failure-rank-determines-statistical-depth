module

public import PaperProofs.Common.NativeRelaxation

/-!
Every measurable native policy with a private seed in any universe has an
equivalent policy whose seed lies in Type 0. The small seed is the entire legal
history rule, with its actual pushed-forward law. This does not assert that
every informal implementation has already been encoded by the native protocol.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem prefix_rule_transport (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed Seed' : Type*}
    (policy : PolicyRule I Seed) (policy' : PolicyRule I Seed') (seed : Seed) (seed' : Seed')
    (hrule : ∀ history, policy seed history = policy' seed' history)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    Prefix input C mode accounting policy' seed' truth tapes n s := by
  induction hp with
  | initial => exact .initial
  | next _ step ih =>
    exact .next ih (hrule _ ▸ step)

def LegalStrategy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) :=
  {rule : List (VisibleEvent I) → Action I //
    LegalRule input C mode accounting (fun (_ : Unit) history => rule history)}

instance legalStrategy_measurableSpace (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) :
    MeasurableSpace (LegalStrategy input C mode accounting) :=
  inferInstanceAs (MeasurableSpace {rule : List (VisibleEvent I) → Action I //
    LegalRule input C mode accounting (fun (_ : Unit) history => rule history)})

def strategyPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) :
    Policy input C mode accounting (LegalStrategy input C mode accounting) where
  rule seed history := seed.val history
  measurable_rule := measurable_from_prod_countable_left (fun history =>
    (measurable_pi_apply history).comp measurable_subtype_coe)
  legal := by
    intro seed truth tapes n s hp hactive
    have hp' := prefix_rule_transport input C mode accounting
      (fun seed : LegalStrategy input C mode accounting => seed.val)
      (fun (_ : Unit) history => seed.val history) seed () (fun _ => rfl) truth tapes hp
    exact seed.property () truth tapes n s hp' hactive

section Encoding

variable {Seed : Type*} [MeasurableSpace Seed]

def encodeSeed (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (seed : Seed) : LegalStrategy input C mode accounting :=
  ⟨policy.rule seed, by
    intro _ truth tapes n s hp hactive
    have hp' := prefix_rule_transport input C mode accounting
      (fun (_ : Unit) history => policy.rule seed history) policy.rule () seed
      (fun _ => rfl) truth tapes hp
    exact policy.legal seed truth tapes n s hp' hactive⟩

theorem measurable_encodeSeed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) :
    Measurable (encodeSeed input C mode accounting policy) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro history
  exact policy.measurable_rule.comp (measurable_id.prodMk measurable_const)

theorem run_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (sample : Seed × input.World) (n : ℕ) :
    run input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) n =
        run input C mode accounting policy.rule sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    rfl

theorem runSuccess_encoded_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (sample : Seed × input.World) :
    runSuccess input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) ↔
        runSuccess input C mode accounting policy.rule sample := by
  simp only [runSuccess, run_encoded_eq]

theorem runActualBill_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (sample : Seed × input.World) :
    runActualBill input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodeSeed input C mode accounting policy sample.1, sample.2) =
        runActualBill input C mode accounting policy.rule sample := by
  simp only [runActualBill, run_encoded_eq]

noncomputable def encodedSeedLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    Measure (LegalStrategy input C mode accounting) :=
  ν.map (encodeSeed input C mode accounting policy)

instance encodedSeedLaw_probability (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (encodedSeedLaw input C mode accounting policy ν) := by
  unfold encodedSeedLaw
  infer_instance

theorem seededWorldLaw_encoded (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    input.seededWorldLaw (encodedSeedLaw input C mode accounting policy ν) =
      (input.seededWorldLaw ν).map (fun sample =>
        (encodeSeed input C mode accounting policy sample.1, sample.2)) := by
  change (ν.map (encodeSeed input C mode accounting policy)).prod input.worldLaw = _
  have h := Measure.map_prod_map ν input.worldLaw
    (measurable_encodeSeed input C mode accounting policy) measurable_id
  rw [Measure.map_id] at h
  change (ν.map (encodeSeed input C mode accounting policy)).prod input.worldLaw =
    (ν.prod input.worldLaw).map (fun sample =>
      (encodeSeed input C mode accounting policy sample.1, sample.2)) at h
  simpa only [StatisticalInput.seededWorldLaw] using h

theorem risk_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    risk input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodedSeedLaw input C mode accounting policy ν) =
        risk input C mode accounting policy.rule ν := by
  unfold risk
  have hm : Measurable (fun sample : Seed × input.World =>
      (encodeSeed input C mode accounting policy sample.1, sample.2)) :=
    ((measurable_encodeSeed input C mode accounting policy).comp measurable_fst).prodMk measurable_snd
  have hs : MeasurableSet {sample | ¬runSuccess input C mode accounting
      (strategyPolicy input C mode accounting).rule sample} :=
    (measurableSet_runSuccess input C mode accounting _
      (strategyPolicy input C mode accounting).measurable_rule).compl
  rw [seededWorldLaw_encoded input C mode accounting policy ν, Measure.map_apply hm hs]
  congr 1
  ext sample
  exact not_congr (runSuccess_encoded_iff input C mode accounting policy sample)

theorem expectedBill_encoded_eq (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    expectedBill input C mode accounting (strategyPolicy input C mode accounting).rule
      (encodedSeedLaw input C mode accounting policy ν) =
        expectedBill input C mode accounting policy.rule ν := by
  unfold expectedBill
  have hm : Measurable (fun sample : Seed × input.World =>
      (encodeSeed input C mode accounting policy sample.1, sample.2)) :=
    ((measurable_encodeSeed input C mode accounting policy).comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_encoded input C mode accounting policy ν,
    lintegral_map
      (measurable_runActualBill input C mode accounting _
        (strategyPolicy input C mode accounting).measurable_rule)
      hm]
  exact lintegral_congr (runActualBill_encoded_eq input C mode accounting policy)

theorem value_le_policy_any_seed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (δ : ℝ≥0∞) (hrisk : risk input C mode accounting policy.rule ν ≤ δ) :
    value input C mode accounting δ ≤ expectedBill input C mode accounting policy.rule ν := by
  rw [← expectedBill_encoded_eq input C mode accounting policy ν]
  apply value_le_policy input C mode accounting δ (encodedSeedLaw input C mode accounting policy ν)
    (strategyPolicy input C mode accounting)
  rw [risk_encoded_eq]
  exact hrisk

/-- One fixed small seed space suffices; only its probability law varies. -/
noncomputable def strategyValue (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (ν : Measure (LegalStrategy input C mode accounting)) (_h : IsProbabilityMeasure ν)
    (_safe : risk input C mode accounting (strategyPolicy input C mode accounting).rule ν ≤ δ),
      expectedBill input C mode accounting (strategyPolicy input C mode accounting).rule ν

theorem value_eq_strategyValue (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    value input C mode accounting δ = strategyValue input C mode accounting δ := by
  apply le_antisymm
  · unfold strategyValue
    refine le_iInf fun ν => le_iInf fun hν => le_iInf fun hsafe => ?_
    let : IsProbabilityMeasure ν := hν
    exact value_le_policy input C mode accounting δ ν (strategyPolicy input C mode accounting) hsafe
  · unfold value
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    have hsafe : risk input C mode accounting (strategyPolicy input C mode accounting).rule
        (encodedSeedLaw input C mode accounting policy.val ν) ≤ δ := by
      rw [risk_encoded_eq]
      exact policy.property
    calc
      _ ≤ expectedBill input C mode accounting (strategyPolicy input C mode accounting).rule
          (encodedSeedLaw input C mode accounting policy.val ν) :=
        iInf_le_of_le (encodedSeedLaw input C mode accounting policy.val ν)
          (iInf_le_of_le (inferInstance : IsProbabilityMeasure
            (encodedSeedLaw input C mode accounting policy.val ν))
            (iInf_le_of_le hsafe le_rfl))
      _ = _ := expectedBill_encoded_eq input C mode accounting policy.val ν

end Encoding
end PaperProofs.Common.Native
