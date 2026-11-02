module

public import PaperProofs.Common.NativeHeadBayes
public import PaperProofs.Common.NativeHeadTotalLower
public import PaperProofs.Common.AvailablePartial
public import PaperProofs.Common.FreshSuffixComposition

/-! The B08 Bellman LOWER bound, first at the fresh head and then at every
original stage, with its independent native value infimum.
The constructive upper half is not asserted here. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

/-- Any policy in the ORIGINAL R-restricted native comparator pays the
independent local-test infimum and Gg shift. This uses its actual Type0 seed
index; the already-proved native seed representation retains all universes. -/
theorem nativeHead_bellman_lower_policy {Seed : Type} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν (ENNReal.ofReal price) :=
  (nativeHead_localValue_lower input head R price hprice policy.val.rule policy.val.measurable_rule ν).trans
    (nativeHead_allPolicy_lower input C hC accounting R policy ν head hhead price hprice)

/-- The same genuine inequality for private seeds in every universe. The
small strategy seed has its actual pushed-forward probability law; the
source's original observations and eventual failure charge are unchanged. -/
theorem nativeHead_bellman_lower_policy_any_seed {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν (ENNReal.ofReal price) := by
  have h := nativeHead_bellman_lower_policy input C hC accounting R
    (availableStrategyPolicy input C accounting R)
    (ν.map (encodeAvailableSeed input C accounting R policy)) head hhead price hprice
  rwa [penaltyObjective_availableEncoded_eq] at h

/-- Finite-paid nonreturn is covered by the proved original partial-rule
totalization; it is never assigned an invented infinite observation fee. -/
theorem nativeHead_bellman_lower_partial_policy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePartialPolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      partialPenaltyObjective input C accounting policy.val.rule ν (ENNReal.ofReal price) := by
  rw [partialPenaltyObjective_eq_totalized]
  exact nativeHead_bellman_lower_policy_any_seed input C hC accounting R
    (policy.totalize input C accounting R) ν head hhead price hprice

/-- Lower bound for the independently defined all-policy healthy value.
No recurrence, optimal-continuation performance, MAP restriction, finite
expected bill or termination property is a premise. -/
theorem healthyPenalty_head_lower (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      input.healthyPenalty 0 R (ENNReal.ofReal price) := by
  change _ ≤ availablePenaltyValue input (currentRelaxedContract I) (zeroNormalAccounting I) R (ENNReal.ofReal price)
  unfold availablePenaltyValue
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact nativeHead_bellman_lower_policy input (currentRelaxedContract I) ⟨rfl, rfl⟩
    (zeroNormalAccounting I) R policy ν head hhead price hprice

theorem healthyPenaltyReal_head_lower (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) :
    input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price) ≤
      input.healthyPenaltyReal 0 R price := by
  have hs : 0 ≤ input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price) :=
    add_nonneg (input.healthyPenaltyReal_nonneg _ _ _) ((input.experiment head).localValueReal_nonneg _)
  have h := ENNReal.toReal_mono (input.healthyPenalty_ne_top 0 R ENNReal.ofReal_ne_top)
    (healthyPenalty_head_lower input head hhead R price hprice)
  simpa only [StatisticalInput.healthyPenaltyReal, ENNReal.toReal_ofReal hs] using h

/-- The lower direction of the frozen Bellman expression at the actual
fresh head. The theorem below transports it to arbitrary suffix indices;
the full CurrentPenaltyRecursion still needs its upper construction. -/
theorem currentPenaltyRecursion_head_lower (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 < price) :
    min price (input.goodPenaltyReal head R price + (input.experiment head).localValueReal
      (input.badPenaltyReal head R price - input.goodPenaltyReal head R price)) ≤
      input.healthyPenaltyReal head.val R price := by
  rw [hhead]
  exact (min_le_right _ _).trans (healthyPenaltyReal_head_lower input head hhead R price hprice.le)

/-- The lower direction of B08 at every original stage, transported from
the genuinely fresh head without changing its policy-infimum value. -/
theorem currentPenaltyRecursion_lower (input : StatisticalInput I) (stage : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 < price) :
    min price (input.goodPenaltyReal stage R price + (input.experiment stage).localValueReal
      (input.badPenaltyReal stage R price - input.goodPenaltyReal stage R price)) ≤
      input.healthyPenaltyReal stage.val R price := by
  apply (input.freshHead_lower_iff stage R price).mp
  exact currentPenaltyRecursion_head_lower (input.freshSuffix stage.val)
    (I.freshHead stage) rfl R price hprice

end PaperProofs.Common.Native
