module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_005
public import PaperProofs.Common.ReferenceSharpNativeUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActualCost122

open Common Common.Native Statistics MeasureTheory Filter
open scoped ENNReal Topology

/-- Convert the true all-path observation domination into the ORIGINAL
whole-variable-bill asymptotics, including corrections on failed paths. -/
theorem referenceExpectedCost_of_observationEnvelope {I : Instance} (input : StatisticalInput I)
    (observationBound : ∀ (C : Contract I) (retained : C.IsEarlyRetained)
      (accounting : NormalAccounting I) (budget : ℚ), 0 < budget → budget ≤ 1/2 →
      expectedObservationBill input C .uncapped accounting
        (idealPolicy input C retained accounting budget).rule (Measure.dirac ()) ≤
        PRetObservationEnvelope119.observationEnvelope input 0 ∅ (budget/2)) :
    ∀ depth : ℕ, girth I = (depth : ℕ∞) → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1/2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (retained : C.IsEarlyRetained) accounting,
          expectedBill input C .uncapped accounting (idealPolicy input C retained accounting budget).rule (Measure.dirac ()) ≤
            ENNReal.ofReal ((1+epsilon)*headCoefficient input*iteratedLog depth (budget : ℝ)⁻¹) := by
  intro depth hgirth epsilon positive
  have coefficientPositive := headCoefficient_pos input (by rw [hgirth]; exact ENat.natCast_ne_top depth)
  let fee : ℝ := (min I.stageCount I.toolCount : ℕ)*input.fees.maxCorrection.toReal
  have feeNonnegative : 0 ≤ fee := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have feeEquality : (min I.stageCount I.toolCount : ℕ)*input.fees.maxCorrection = ENNReal.ofReal fee := by
    dsimp only [fee]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal (ne_of_lt input.fees.maxCorrection_lt_top)]
  have growth : Tendsto (fun budget : ℚ => iteratedLog depth (1/(budget : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    (iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop
  have coefficient : 0 < (epsilon/2)*headCoefficient input := mul_pos (by positivity) coefficientPositive
  have absorb := (growth.const_mul_atTop coefficient).eventually_ge_atTop fee
  have positiveLog := growth.eventually_gt_atTop 0
  obtain ⟨feeCutoff, feePositive, feeBound⟩ := rationalEventually_positive_cutoff (absorb.and positiveLog)
  obtain ⟨envelopeCutoff, envelopePositive, envelopeBound⟩ :=
    PRetObservationEnvelope119.observationEnvelopeAsymptotics input depth hgirth (epsilon/2) (by positivity)
  refine ⟨min feeCutoff envelopeCutoff, lt_min feePositive envelopePositive, ?_⟩
  intro budget budgetPositive budgetSmall below C retained accounting
  obtain ⟨absorption, logPositive⟩ := feeBound budget budgetPositive (below.trans_le (min_le_left _ _))
  have envelope := envelopeBound budget budgetPositive budgetSmall (below.trans_le (min_le_right _ _))
  have costs := (observationBound C retained accounting budget budgetPositive budgetSmall).trans envelope
  have leadingNonnegative : 0 ≤ (1+epsilon/2)*headCoefficient input*iteratedLog depth (budget : ℝ)⁻¹ := by
    have : 0 < iteratedLog depth (budget : ℝ)⁻¹ := by simpa only [one_div] using logPositive
    positivity
  calc
    _ ≤ expectedObservationBill input C .uncapped accounting
        (idealPolicy input C retained accounting budget).rule (Measure.dirac ()) +
        (min I.stageCount I.toolCount : ℕ)*input.fees.maxCorrection :=
      expectedBill_le_observation_add input C .uncapped accounting (idealPolicy input C retained accounting budget) (Measure.dirac ())
    _ ≤ ENNReal.ofReal ((1+epsilon/2)*headCoefficient input*iteratedLog depth (budget : ℝ)⁻¹) + ENNReal.ofReal fee :=
      add_le_add costs feeEquality.le
    _ = ENNReal.ofReal ((1+epsilon/2)*headCoefficient input*iteratedLog depth (budget : ℝ)⁻¹ + fee) :=
      (ENNReal.ofReal_add leadingNonnegative feeNonnegative).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [one_div] using (show
      (1+epsilon/2)*headCoefficient input*iteratedLog depth (1/(budget : ℝ)) + fee ≤
        (1+epsilon)*headCoefficient input*iteratedLog depth (1/(budget : ℝ)) by nlinarith only [absorption]))

end PaperProofs.Retained.PRetActualCost122
