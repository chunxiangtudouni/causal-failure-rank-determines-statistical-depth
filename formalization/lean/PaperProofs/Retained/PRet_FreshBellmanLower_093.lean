module

public import PaperProofs.Retained.PRet_FreshHeadTotal_091
public import PaperProofs.Retained.PRet_FreshTerminalLower_092
public import PaperProofs.Retained.PRet_FreshBellmanBounds_077

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshBellmanLower093

open Common Common.Native MeasureTheory PRetFreshHeadTotal091 PRetFreshTerminalLower092
open PRetGenericHeadBayes082 PRetFreshLocalPrices042 PRetAmbientComparator073 PRetGenericHeadWeights089
open scoped ENNReal

variable {I : Instance}

theorem fresh_lower_policy {Seed : Type} [MeasurableSpace Seed]
    (input : StatisticalInput I) (original : I.Stage) (old : Finset I.Stage) (hhealthy : Healthy I original.val old)
    (source : Policy (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix original.val)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ) (hp : 0 ≤ penalty) :
    ENNReal.ofReal (goodPenaltyReal input original old penalty + (input.experiment original).localValueReal
      (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty)) ≤
        freshObjective input original.val old source.rule ν (ENNReal.ofReal penalty) := by
  classical
  by_cases hend : I.stageCount ≤ original.val + 1
  · exact terminal_policy_lower input original old hhealthy hend source ν penalty hp
  · let localInput := input.freshSuffix original.val
    let head := I.freshHead original
    let next : (I.freshSuffix original.val).Stage := ⟨1, by
      change 1 < (I.freshSuffix original.val).stageCount
      rw [I.freshSuffix_stageCount]
      have hi := original.isLt
      omega⟩
    have hexp : localInput.experiment head = input.experiment original := by
      rw [StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]
    have hl := shifted_localValue_lower localInput head source.rule source.measurable_rule ν
      (goodPenaltyReal input original old penalty) (badPenaltyReal input original old penalty)
      (goodPenalty_nonneg input original old penalty) (goodPenalty_le_badPenalty input original old penalty hp)
    have ht := integrated_head_lower input original old source ν next rfl penalty hp
    have hsame :
        (∫⁻ sample, (localInput.experiment head).observationCharge
          ((nativeHeadTest localInput head source.rule source.measurable_rule).rule.stop sample.1 (worldTapes localInput sample.2 head)) +
          (if (nativeHeadTest localInput head source.rule source.measurable_rule).rule.decision sample.1 (worldTapes localInput sample.2 head) =
            localInput.truthAt sample.2 head then ENNReal.ofReal (goodPenaltyReal input original old penalty)
            else ENNReal.ofReal (badPenaltyReal input original old penalty)) ∂localInput.seededWorldLaw ν) =
        (∫⁻ sample, (localInput.experiment head).observationCharge
          (headExitStop localInput head source.rule sample.1 (worldTapes localInput sample.2 head)) +
          decisionWeight localInput head source.rule (goodPenaltyReal input original old penalty)
            (badPenaltyReal input original old penalty) sample ∂localInput.seededWorldLaw ν) := by
      apply lintegral_congr
      intro sample
      rfl
    rw [hsame] at hl
    have hcomb := hl.trans ht
    rw [hexp] at hcomb
    simpa only [freshObjective_eq_jointObjective] using hcomb

/-- The independently defined ORIGINAL full-policy infimum pays the true
old-H shifted local expression. No Bellman definition/attained optimizer is
used; this is the constructive lower direction only. -/
theorem freshPenalty_lower (input : StatisticalInput I) (original : I.Stage)
    (old : Finset I.Stage) (hhealthy : Healthy I original.val old) (penalty : ℝ) (hp : 0 ≤ penalty) :
    ENNReal.ofReal (goodPenaltyReal input original old penalty + (input.experiment original).localValueReal
      (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty)) ≤
        freshPenalty input original.val old (ENNReal.ofReal penalty) := by
  unfold freshPenalty
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact fresh_lower_policy input original old hhealthy policy ν penalty hp

theorem freshPenaltyReal_lower (input : StatisticalInput I) (original : I.Stage)
    (old : Finset I.Stage) (hhealthy : Healthy I original.val old) (penalty : ℝ) (hp : 0 ≤ penalty) :
    goodPenaltyReal input original old penalty + (input.experiment original).localValueReal
      (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty) ≤
        freshPenaltyReal input original.val old penalty := by
  have hnonneg := add_nonneg (goodPenalty_nonneg input original old penalty)
    ((input.experiment original).localValueReal_nonneg (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty))
  have h := ENNReal.toReal_mono (freshPenalty_ne_top input original.val old ENNReal.ofReal_ne_top)
    (freshPenalty_lower input original old hhealthy penalty hp)
  simpa only [freshPenaltyReal, ENNReal.toReal_ofReal hnonneg] using h

theorem original_recursion_lower (input : StatisticalInput I) (original : I.Stage)
    (old : Finset I.Stage) (hhealthy : Healthy I original.val old) (penalty : ℝ) (hp : 0 < penalty) :
    min penalty (goodPenaltyReal input original old penalty + (input.experiment original).localValueReal
      (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty)) ≤
        freshPenaltyReal input original.val old penalty :=
  (min_le_right _ _).trans (freshPenaltyReal_lower input original old hhealthy penalty hp.le)

end PaperProofs.Retained.PRetFreshBellmanLower093
