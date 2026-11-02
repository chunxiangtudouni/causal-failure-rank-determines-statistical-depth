module

public import PaperProofs.Common.AvailableValue
public import PaperProofs.Common.NativePartial

/-!
Nonreturned actions in the same R-restricted healthy-policy comparator.
Totalization is abandonment with the entire previous bill retained. Neither
availability nor a penalty infimum excludes a partial strategy of finite cost.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

def PartialUsesOnly (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (policy : PartialRule I Seed) (available : Finset I.Tool) : Prop :=
  ∀ (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I),
    PartialPrefix input C .uncapped accounting policy seed truth tapes n s → s.halted = false →
      ∀ (handle : MismatchHandle I) (tool : I.Tool),
        policy seed s.history = some (.allocate handle tool) → tool ∈ available

theorem partialUsesOnly_iff_totalized (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (available : Finset I.Tool) :
    PartialUsesOnly input C accounting policy available ↔
      UsesOnly input C accounting (totalizeRule policy) available := by
  constructor
  · intro h seed truth tapes n s hp ha handle tool heq
    have hpp := (partialPrefix_iff_totalized input C .uncapped accounting policy seed truth tapes n s).mpr hp
    cases haction : policy seed s.history with
    | none =>
      simp only [totalizeRule, haction, Option.getD_none] at heq
      cases heq
    | some action =>
      have heqa : action = .allocate handle tool := by
        simpa only [totalizeRule, haction, Option.getD_some] using heq
      exact h seed truth tapes n s hpp ha handle tool (haction.trans (congrArg some heqa))
  · intro h seed truth tapes n s hp ha handle tool heq
    have hpt := (partialPrefix_iff_totalized input C .uncapped accounting policy seed truth tapes n s).mp hp
    apply h seed truth tapes n s hpt ha handle tool
    simp only [totalizeRule, heq, Option.getD_some]

noncomputable def partialRunObservationBill (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, (partialRun input C .uncapped accounting policy sample n).ledger.observationBill input.fees

theorem partialRunObservationBill_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (sample : Seed × input.World) :
    partialRunObservationBill input C accounting policy sample =
      runObservationBill input C .uncapped accounting (totalizeRule policy) sample := by
  simp only [partialRunObservationBill, runObservationBill, partialRun_eq_totalized]

section Measurable

variable [MeasurableSpace Seed]

abbrev AvailablePartialPolicy (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (Seed : Type*)
    [MeasurableSpace Seed] :=
  {policy : PartialPolicy input C .uncapped accounting Seed //
    PartialUsesOnly input C accounting policy.rule available}

def AvailablePartialPolicy.totalize (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePartialPolicy input C accounting available Seed) :
    AvailablePolicy input C accounting available Seed :=
  ⟨policy.val.totalize input C .uncapped accounting,
    (partialUsesOnly_iff_totalized input C accounting policy.val.rule available).mp policy.property⟩

def AvailablePolicy.partialize (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Seed) :
    AvailablePartialPolicy input C accounting available Seed := by
  refine ⟨policy.val.partialize input C .uncapped accounting, ?_⟩
  apply (partialUsesOnly_iff_totalized input C accounting _ available).mpr
  simpa only [totalize_partialize_rule] using policy.property

noncomputable def partialExpectedObservationBill (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, partialRunObservationBill input C accounting policy sample ∂input.seededWorldLaw ν

theorem partialExpectedObservationBill_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (ν : Measure Seed) :
    partialExpectedObservationBill input C accounting policy ν =
      expectedObservationBill input C .uncapped accounting (totalizeRule policy) ν := by
  simp only [partialExpectedObservationBill, expectedObservationBill, partialRunObservationBill_eq_totalized]

noncomputable def partialPenaltyObjective (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  partialExpectedObservationBill input C accounting policy ν +
    penalty * partialRisk input C .uncapped accounting policy ν

theorem partialPenaltyObjective_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    partialPenaltyObjective input C accounting policy ν penalty =
      penaltyObjective input C .uncapped accounting (totalizeRule policy) ν penalty := by
  simp only [partialPenaltyObjective, penaltyObjective, partialExpectedObservationBill_eq_totalized,
    partialRisk_eq_totalized]

theorem availablePenaltyValue_le_partialPolicy_any_seed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePartialPolicy input C accounting available Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    availablePenaltyValue input C accounting available penalty ≤
      partialPenaltyObjective input C accounting policy.val.rule ν penalty := by
  rw [partialPenaltyObjective_eq_totalized]
  exact availablePenaltyValue_le_policy_any_seed input C accounting available penalty ν
    (policy.totalize input C accounting available)

end Measurable

noncomputable def availablePartialPenaltyValue (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (SmallSeed : Type), ⨅ (m : MeasurableSpace SmallSeed),
    let : MeasurableSpace SmallSeed := m
    ⨅ (ν : Measure SmallSeed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : AvailablePartialPolicy input C accounting available SmallSeed,
        partialPenaltyObjective input C accounting policy.val.rule ν penalty

theorem availablePartialPenaltyValue_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞) :
    availablePartialPenaltyValue input C accounting available penalty =
      availablePenaltyValue input C accounting available penalty := by
  apply le_antisymm
  · conv_rhs => unfold availablePenaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    let partialPolicy := policy.partialize input C accounting available
    have hle : availablePartialPenaltyValue input C accounting available penalty ≤
        partialPenaltyObjective input C accounting partialPolicy.val.rule ν penalty := by
      unfold availablePartialPenaltyValue
      exact iInf_le_of_le SmallSeed (iInf_le_of_le m (iInf_le_of_le ν
        (iInf_le_of_le hν (iInf_le_of_le partialPolicy le_rfl))))
    simpa only [partialPolicy, AvailablePolicy.partialize, partialPenaltyObjective_eq_totalized,
      totalize_partialize_rule] using hle
  · conv_rhs => unfold availablePartialPenaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    exact le_iInf fun policy => availablePenaltyValue_le_partialPolicy_any_seed input C accounting
      available policy ν penalty

end PaperProofs.Common.Native
