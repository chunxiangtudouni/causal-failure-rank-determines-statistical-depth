module

public import PaperProofs.Retained.PRet_FreshHeadFailure_088
public import PaperProofs.Retained.PRet_GenericHeadBayes_082
public import PaperProofs.Retained.PRet_FreshTerminalBoundary_040
public import PaperProofs.Retained.PRet_FreshBranchValues_084

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshTerminalLower092

open Common Common.Native MeasureTheory PRetFreshHeadFailure088 PRetGenericHeadBayes082
open PRetFreshTerminalBoundary040 PRetFreshBranchValues084 PRetAmbientComparator073 PRetJointCharges075
open scoped ENNReal

variable {I : Instance} {Seed : Type} [MeasurableSpace Seed]

/-- Genuine one-stage boundary of the full fresh-policy lower comparison.
A correct head keeps old H; an unmatchable wrong insertion pays the original
failure charge, regardless of actual physical payments or later nonreturn. -/
theorem terminal_policy_lower (input : StatisticalInput I) (original : I.Stage) (old : Finset I.Stage)
    (hhealthy : Healthy I original.val old) (hend : I.stageCount ≤ original.val + 1)
    (source : Policy (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix original.val)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ) (hp : 0 ≤ penalty) :
    ENNReal.ofReal (goodPenaltyReal input original old penalty + (input.experiment original).localValueReal
      (badPenaltyReal input original old penalty - goodPenaltyReal input original old penalty)) ≤
        freshObjective input original.val old source.rule ν (ENNReal.ofReal penalty) := by
  classical
  let localInput := input.freshSuffix original.val
  let head := I.freshHead original
  have hgood : goodPenaltyReal input original old penalty = 0 := by
    unfold goodPenaltyReal freshPenaltyReal
    rw [freshPenalty_past_end input (original.val + 1) hend old hhealthy.2.2, ENNReal.toReal_zero]
  have hexp : localInput.experiment head = input.experiment original := by
    rw [StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]
  rw [freshObjective_eq_jointObjective]
  by_cases hm : Matchable I (insert original old)
  · have hbad : badPenaltyReal input original old penalty = 0 := by
      rw [badPenaltyReal_eq_inserted input original old penalty hp]
      unfold freshPenaltyReal
      rw [freshPenalty_past_end input (original.val + 1) hend (insert original old) hm, ENNReal.toReal_zero]
    simp only [hgood, hbad, sub_zero, add_zero, Statistics.BinaryExperiment.localValueReal,
      ENNReal.ofReal_zero, Statistics.BinaryExperiment.localValue_zero, ENNReal.toReal_zero]
    exact bot_le
  · have hbad : badPenaltyReal input original old penalty = penalty := by
      simp only [badPenaltyReal, hm, ↓reduceIte]
    have hl := shifted_localValue_lower localInput head source.rule source.measurable_rule ν 0 penalty (le_refl 0) hp
    have hbadHead : ¬ Matchable I (insert (I.freshStageLift original.val head) old) := by
      rw [Instance.freshStageLift_freshHead]
      exact hm
    have hpay : (∫⁻ sample, (localInput.experiment head).observationCharge
        ((nativeHeadTest localInput head source.rule source.measurable_rule).rule.stop sample.1 (worldTapes localInput sample.2 head)) +
        (if (nativeHeadTest localInput head source.rule source.measurable_rule).rule.decision sample.1 (worldTapes localInput sample.2 head) =
          localInput.truthAt sample.2 head then ENNReal.ofReal 0 else ENNReal.ofReal penalty) ∂localInput.seededWorldLaw ν) ≤
        jointObjective localInput (I.freshStageLift original.val) old source.rule ν (ENNReal.ofReal penalty) := by
      rw [jointObjective_eq_lintegral _ _ _ _ source.measurable_rule]
      apply lintegral_mono
      intro sample
      simpa only [nativeHeadTest, ENNReal.ofReal_zero] using
        unmatchable_head_charge_lower localInput source (I.freshStageLift original.val) old head rfl hbadHead sample (ENNReal.ofReal penalty)
    calc
      _ = ENNReal.ofReal (0 + (localInput.experiment head).localValueReal (penalty - 0)) := by rw [hgood, hbad, hexp]
      _ ≤ _ := hl.trans hpay

end PaperProofs.Retained.PRetFreshTerminalLower092
