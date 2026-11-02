module

public import PaperProofs.Retained.PRet_FreshExpectation_113
public import PaperProofs.Retained.PRet_NestedChildPolicy_095
public import PaperProofs.Retained.PRet_FreshNearOpt_069
public import PaperProofs.Retained.PRet_FreshBranchValues_084
public import PaperProofs.Common.NativeBellmanValueUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshBellmanUpper114

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetFreshLocalPrices042 PRetFreshNearOpt069
open PRetFreshBranchValues084 PRetNestedChildPolicy095 PRetFreshIndependentPolicy112 PRetFreshExpectation113
open BellmanPrivateSeeds
open scoped ENNReal

variable {I : Instance}

/-- The ORIGINAL full fresh infimum is bounded by the shifted local value.
All three near-optimizers are selected from independent genuine infima and
implemented by the actual same-interpreter product policy. -/
theorem freshPenalty_upper (input : StatisticalInput I) (original : I.Stage)
    (old : Finset I.Stage) (price : ℝ) (hprice : 0 ≤ price) :
    freshPenalty input original.val old (ENNReal.ofReal price) ≤
      ENNReal.ofReal (goodPenaltyReal input original old price + (input.experiment original).localValueReal
        (badPenaltyReal input original old price - goodPenaltyReal input original old price)) := by
  classical
  let J := I.freshSuffix original.val
  let localInput := input.freshSuffix original.val
  let head := I.freshHead original
  let E := localInput.experiment head
  let g := goodPenaltyReal input original old price
  let b := badPenaltyReal input original old price
  have hexp : E = input.experiment original := by
    change (input.freshSuffix original.val).experiment (I.freshHead original) = input.experiment original
    rw [StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]
  have ho : 0 ≤ g ∧ g ≤ b ∧ b ≤ price :=
    ⟨goodPenalty_nonneg input original old price,
      goodPenalty_le_badPenalty input original old price hprice,
      badPenalty_le_penalty input original old price hprice⟩
  have hj : ENNReal.ofReal (E.localValueReal (b - g)) = E.localValue (ENNReal.ofReal (b - g)) :=
    ENNReal.ofReal_toReal (E.localValue_ofReal_ne_top (b - g))
  change freshPenalty input original.val old (ENNReal.ofReal price) ≤ ENNReal.ofReal (g + (input.experiment original).localValueReal (b - g))
  rw [← hexp, ENNReal.ofReal_add ho.1 (E.localValueReal_nonneg (b - g)), hj]
  apply bellman_le_of_forall_two_epsilon
  intro epsilon hepsilon
  obtain ⟨Local, mLocal, localRest⟩ := exists_localObjective_near E (ENNReal.ofReal (b - g))
    ENNReal.ofReal_ne_top epsilon hepsilon
  let : MeasurableSpace Local := mLocal
  obtain ⟨localLaw, hLocal, test, htest⟩ := localRest
  let : IsProbabilityMeasure localLaw := hLocal
  obtain ⟨Good, mGood, goodRest⟩ := exists_freshObjective_near input (original.val + 1) old
    (ENNReal.ofReal price) ENNReal.ofReal_ne_top epsilon hepsilon
  let : MeasurableSpace Good := mGood
  obtain ⟨goodLaw, hGood, good, hgoodNear⟩ := goodRest
  let : IsProbabilityMeasure goodLaw := hGood
  obtain ⟨Bad, mBad, badRest⟩ := exists_freshObjective_near input (original.val + 1) (insert original old)
    (ENNReal.ofReal price) ENNReal.ofReal_ne_top epsilon hepsilon
  let : MeasurableSpace Bad := mBad
  obtain ⟨badLaw, hBad, bad, hbadNear⟩ := badRest
  let : IsProbabilityMeasure badLaw := hBad
  let good' := nestedPolicy input original.val 1 good
  let bad' := nestedPolicy input original.val 1 bad
  let embed := fun stage : (J.freshSuffix 1).Stage => I.freshStageLift original.val (J.freshStageLift 1 stage)
  have hgoodCost : jointObjective (localInput.freshSuffix 1) embed old good'.rule goodLaw (ENNReal.ofReal price) ≤
      ENNReal.ofReal (g + epsilon) := by
    calc
      _ = freshObjective input (original.val + 1) old good.rule goodLaw (ENNReal.ofReal price) :=
        nestedPolicy_objective_eq input original.val 1 old good goodLaw (ENNReal.ofReal price)
      _ ≤ _ := by
        have hvalue : freshPenalty input (original.val + 1) old (ENNReal.ofReal price) = ENNReal.ofReal g :=
          (ofReal_goodPenaltyReal input original old price).symm
        rw [ENNReal.ofReal_add ho.1 hepsilon.le, ← hvalue]
        exact hgoodNear.le
  have hbadCost : jointObjective (localInput.freshSuffix 1) embed (insert original old) bad'.rule badLaw (ENNReal.ofReal price) ≤
      ENNReal.ofReal (b + epsilon) := by
    calc
      _ = freshObjective input (original.val + 1) (insert original old) bad.rule badLaw (ENNReal.ofReal price) :=
        nestedPolicy_objective_eq input original.val 1 (insert original old) bad badLaw (ENNReal.ofReal price)
      _ ≤ _ := by
        have hvalue : freshPenalty input (original.val + 1) (insert original old) (ENNReal.ofReal price) = ENNReal.ofReal b :=
          (ofReal_badPenaltyReal input original old price hprice).symm
        rw [ENNReal.ofReal_add (ho.1.trans ho.2.1) hepsilon.le, ← hvalue]
        exact hbadNear.le
  let policy := independentPolicy localInput head test good' bad'
  have hinf := freshPenalty_le_policy input original.val old (ENNReal.ofReal price) (combinedLaw localLaw goodLaw badLaw) policy
  change freshPenalty input original.val old (ENNReal.ofReal price) ≤
    jointObjective localInput (I.freshStageLift original.val) old policy.rule (combinedLaw localLaw goodLaw badLaw) (ENNReal.ofReal price) at hinf
  have hfinite : E.bayesObjective localLaw test (ENNReal.ofReal (b - g)) ≠ ⊤ := ne_of_lt (htest.trans_le le_top)
  have hparent := independent_objective_upper localInput head rfl localLaw goodLaw badLaw test good' bad'
    (I.freshStageLift original.val) old (ENNReal.ofReal (b - g)) (ENNReal.ofReal price) hfinite
  have hembed : I.freshStageLift original.val head = original := I.freshStageLift_freshHead original
  rw [hembed] at hparent
  have hweights := BellmanExpectation.correctMass_add_bayesError localInput head localLaw test
  have hmix := bellman_mixture_le_shifted_bayes E localLaw test ho.1 ho.2.1 hepsilon.le hweights hgoodCost hbadCost
  have hbound := hinf.trans hparent
  have hbound' := hbound.trans (by simpa only [add_assoc] using hmix)
  exact hbound'.trans (by
    have ht := add_le_add (add_le_add (le_refl (ENNReal.ofReal g)) htest.le) (le_refl (ENNReal.ofReal epsilon))
    simpa only [add_assoc] using ht)

end PaperProofs.Retained.PRetFreshBellmanUpper114
