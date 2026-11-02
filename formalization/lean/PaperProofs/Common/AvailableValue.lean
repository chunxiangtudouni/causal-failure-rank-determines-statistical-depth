module

public import PaperProofs.Common.NativePenalty

/-!
The same real native policies with a fixed set of initially available tools.
`UsesOnly` is a legality requirement on reached allocation actions, not a risk,
cost or performance assumption. In particular it also applies after failure.
The infimum retains private randomization and non-MAP writes. A small seed
representation below proves that its universe does not exclude large seeds.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

def UsesOnly (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (policy : PolicyRule I Seed) (available : Finset I.Tool) : Prop :=
  ∀ (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I),
    Prefix input C .uncapped accounting policy seed truth tapes n s → s.halted = false →
      ∀ (handle : MismatchHandle I) (tool : I.Tool),
        policy seed s.history = .allocate handle tool → tool ∈ available

theorem usesOnly_univ (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) :
    UsesOnly input C accounting policy Finset.univ := by
  intro _ _ _ _ _ _ _ _ tool _
  exact Finset.mem_univ tool

theorem UsesOnly.mono (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    {available larger : Finset I.Tool} (h : UsesOnly input C accounting policy available)
    (hsub : available ⊆ larger) : UsesOnly input C accounting policy larger := by
  intro seed truth tapes n s hp ha handle tool heq
  exact hsub (h seed truth tapes n s hp ha handle tool heq)

abbrev AvailablePolicy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (Seed : Type*)
    [MeasurableSpace Seed] :=
  {policy : Policy input C .uncapped accounting Seed // UsesOnly input C accounting policy.rule available}

abbrev AvailableStrategy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) :=
  {strategy : LegalStrategy input C .uncapped accounting //
    UsesOnly input C accounting (fun (_ : Unit) history => strategy.val history) available}

def availableStrategyPolicy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) :
    AvailablePolicy input C accounting available (AvailableStrategy input C accounting available) := by
  refine ⟨{rule := fun seed history => seed.val.val history, measurable_rule := ?_, legal := ?_}, ?_⟩
  · apply measurable_from_prod_countable_left
    intro history
    exact (measurable_pi_apply history).comp
      (measurable_subtype_coe.comp measurable_subtype_coe)
  · intro strategy truth tapes n s hp ha
    have hp' := prefix_rule_transport input C .uncapped accounting
      (fun seed : AvailableStrategy input C accounting available => seed.val.val)
      (fun (_ : Unit) history => strategy.val.val history) strategy () (fun _ => rfl) truth tapes hp
    exact strategy.val.property () truth tapes n s hp' ha
  · intro strategy truth tapes n s hp ha handle tool heq
    have hp' := prefix_rule_transport input C .uncapped accounting
      (fun seed : AvailableStrategy input C accounting available => seed.val.val)
      (fun (_ : Unit) history => strategy.val.val history) strategy () (fun _ => rfl) truth tapes hp
    exact strategy.property () truth tapes n s hp' ha handle tool heq

section Seed

variable [MeasurableSpace Seed]

def encodeAvailableSeed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Seed) (seed : Seed) :
    AvailableStrategy input C accounting available :=
  ⟨encodeSeed input C .uncapped accounting policy.val seed, by
    intro _ truth tapes n s hp ha handle tool heq
    have hp' := prefix_rule_transport input C .uncapped accounting
      (fun (_ : Unit) history => policy.val.rule seed history) policy.val.rule () seed
      (fun _ => rfl) truth tapes hp
    exact policy.property seed truth tapes n s hp' ha handle tool heq⟩

theorem measurable_encodeAvailableSeed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Seed) :
    Measurable (encodeAvailableSeed input C accounting available policy) :=
  (measurable_encodeSeed input C .uncapped accounting policy.val).subtype_mk

theorem run_availableEncoded_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Seed) (sample : Seed × input.World) (n : ℕ) :
    run input C .uncapped accounting (availableStrategyPolicy input C accounting available).val.rule
      (encodeAvailableSeed input C accounting available policy sample.1, sample.2) n =
        run input C .uncapped accounting policy.val.rule sample n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih]; rfl

theorem seededWorldLaw_map_seed {Seed' : Type*} [MeasurableSpace Seed']
    (input : StatisticalInput I) (ν : Measure Seed) (f : Seed → Seed') (hf : Measurable f) :
    input.seededWorldLaw (ν.map f) =
      (input.seededWorldLaw ν).map (fun sample => (f sample.1, sample.2)) := by
  have h := Measure.map_prod_map ν input.worldLaw hf measurable_id
  rw [Measure.map_id] at h
  change (ν.map f).prod input.worldLaw =
    (ν.prod input.worldLaw).map (fun sample => (f sample.1, sample.2)) at h
  simpa only [StatisticalInput.seededWorldLaw] using h

theorem penaltyObjective_availableEncoded_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    penaltyObjective input C .uncapped accounting
      (availableStrategyPolicy input C accounting available).val.rule
      (ν.map (encodeAvailableSeed input C accounting available policy)) penalty =
        penaltyObjective input C .uncapped accounting policy.val.rule ν penalty := by
  have hsuccess (sample : Seed × input.World) :
      runSuccess input C .uncapped accounting (availableStrategyPolicy input C accounting available).val.rule
        (encodeAvailableSeed input C accounting available policy sample.1, sample.2) ↔
          runSuccess input C .uncapped accounting policy.val.rule sample := by
    simp only [runSuccess, run_availableEncoded_eq]
  have hbill (sample : Seed × input.World) :
      runObservationBill input C .uncapped accounting
        (availableStrategyPolicy input C accounting available).val.rule
        (encodeAvailableSeed input C accounting available policy sample.1, sample.2) =
          runObservationBill input C .uncapped accounting policy.val.rule sample := by
    simp only [runObservationBill, run_availableEncoded_eq]
  have hm : Measurable (fun sample : Seed × input.World =>
      (encodeAvailableSeed input C accounting available policy sample.1, sample.2)) :=
    ((measurable_encodeAvailableSeed input C accounting available policy).comp measurable_fst).prodMk measurable_snd
  have hcost : expectedObservationBill input C .uncapped accounting
      (availableStrategyPolicy input C accounting available).val.rule
        (ν.map (encodeAvailableSeed input C accounting available policy)) =
      expectedObservationBill input C .uncapped accounting policy.val.rule ν := by
    unfold expectedObservationBill
    rw [seededWorldLaw_map_seed input ν _ (measurable_encodeAvailableSeed input C accounting available policy),
      lintegral_map (measurable_runObservationBill input C .uncapped accounting _
        (availableStrategyPolicy input C accounting available).val.measurable_rule) hm]
    exact lintegral_congr hbill
  have hrisk : risk input C .uncapped accounting
      (availableStrategyPolicy input C accounting available).val.rule
        (ν.map (encodeAvailableSeed input C accounting available policy)) =
      risk input C .uncapped accounting policy.val.rule ν := by
    unfold risk
    have hs : MeasurableSet {sample | ¬runSuccess input C .uncapped accounting
        (availableStrategyPolicy input C accounting available).val.rule sample} :=
      (measurableSet_runSuccess input C .uncapped accounting _
        (availableStrategyPolicy input C accounting available).val.measurable_rule).compl
    rw [seededWorldLaw_map_seed input ν _ (measurable_encodeAvailableSeed input C accounting available policy),
      Measure.map_apply hm hs]
    congr 1
    ext sample
    exact not_congr (hsuccess sample)
  unfold penaltyObjective
  rw [hcost, hrisk]

end Seed

noncomputable def availablePenaltyValue (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (SmallSeed : Type), ⨅ (m : MeasurableSpace SmallSeed),
    letI : MeasurableSpace SmallSeed := m
    ⨅ (ν : Measure SmallSeed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : AvailablePolicy input C accounting available SmallSeed,
        penaltyObjective input C .uncapped accounting policy.val.rule ν penalty

theorem availablePenaltyValue_le_policy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞)
    {SmallSeed : Type} [MeasurableSpace SmallSeed] (ν : Measure SmallSeed) [IsProbabilityMeasure ν]
    (policy : AvailablePolicy input C accounting available SmallSeed) :
    availablePenaltyValue input C accounting available penalty ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν penalty := by
  exact iInf_le_of_le SmallSeed (iInf_le_of_le ‹MeasurableSpace SmallSeed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν› (iInf_le_of_le policy le_rfl))))

theorem availablePenaltyValue_le_policy_any_seed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞)
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : AvailablePolicy input C accounting available Seed) :
    availablePenaltyValue input C accounting available penalty ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν penalty := by
  have h := availablePenaltyValue_le_policy input C accounting available penalty
    (ν.map (encodeAvailableSeed input C accounting available policy))
    (availableStrategyPolicy input C accounting available)
  rwa [penaltyObjective_availableEncoded_eq] at h

theorem availablePenaltyValue_antitone (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) :
    Antitone (fun available => availablePenaltyValue input C accounting available penalty) := by
  intro smaller larger hsub
  conv_rhs => unfold availablePenaltyValue
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact availablePenaltyValue_le_policy input C accounting larger penalty ν
    ⟨policy.val, UsesOnly.mono input C accounting policy.val.rule policy.property hsub⟩

theorem availablePenaltyValue_univ (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) :
    availablePenaltyValue input C accounting Finset.univ penalty = penaltyValue input C accounting penalty := by
  apply le_antisymm
  · conv_rhs => unfold penaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    exact le_iInf fun policy => availablePenaltyValue_le_policy input C accounting Finset.univ penalty ν
      ⟨policy, usesOnly_univ input C accounting policy.rule⟩
  · conv_rhs => unfold availablePenaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    exact le_iInf fun policy => penaltyValue_le_policy input C accounting penalty ν policy.val

theorem abandonPolicy_usesOnly (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (Seed : Type*) [MeasurableSpace Seed] :
    UsesOnly input C accounting (abandonPolicy input C .uncapped accounting Seed).rule available := by
  intro _ _ _ _ _ _ _ _ _ heq
  cases heq

theorem availablePenaltyValue_le_penalty (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞) :
    availablePenaltyValue input C accounting available penalty ≤ penalty := by
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := availablePenaltyValue_le_policy input C accounting available penalty ν
    ⟨abandonPolicy input C .uncapped accounting Unit, abandonPolicy_usesOnly input C accounting available Unit⟩
  change availablePenaltyValue input C accounting available penalty ≤
    penaltyObjective input C .uncapped accounting (abandonPolicy input C .uncapped accounting Unit).rule ν penalty at h
  rw [penaltyObjective, abandon_expectedObservationBill, zero_add] at h
  have hr : risk input C .uncapped accounting
      (abandonPolicy input C .uncapped accounting Unit).rule ν ≤ 1 := prob_le_one
  have hmul : penalty * risk input C .uncapped accounting
      (abandonPolicy input C .uncapped accounting Unit).rule ν ≤ penalty := by
    simpa only [mul_one] using mul_le_mul_right hr penalty
  exact h.trans hmul

end PaperProofs.Common.Native
