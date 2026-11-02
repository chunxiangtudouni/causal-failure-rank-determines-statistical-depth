module

public import PaperProofs.Retained.Controller
public import PaperProofs.Common.ReferenceSharpNativeUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNativeUpper121

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal

/-- The original retained native upper law from its two original actual
script interfaces. No cost, termination or risk condition is added to the
policy comparator or to the original H0 qualification. -/
theorem nativeUpperPriceLaw_of_interfaces {I : Instance} (input : StatisticalInput I)
    (riskCost : ReferenceRiskAndCost input)
    (truncation : TruncationAndNativeImplementation input) : NativeUpperPriceLaw input := by
  intro depth hgirth epsilon positive
  have finite : girth I ≠ ⊤ := by rw [hgirth]; exact ENat.natCast_ne_top depth
  have coefficientPositive := headCoefficient_pos input finite
  have depthPositive : 1 ≤ depth := by
    have bound := one_le_girth I
    rw [hgirth] at bound
    exact_mod_cast bound
  let eta := min (epsilon/4) 1
  have etaPositive : 0 < eta := lt_min (by positivity) (by norm_num)
  have etaOne : eta ≤ 1 := min_le_right _ _
  have etaEpsilon : eta ≤ epsilon/4 := min_le_left _ _
  have product : (1+eta)*(1+eta) ≤ 1+epsilon := by
    have square : eta*eta ≤ eta := by nlinarith
    nlinarith
  obtain ⟨costCutoff, costPositive, costBound⟩ := riskCost.2 depth hgirth eta etaPositive
  obtain ⟨logCutoff, logPositive, logBound⟩ := iteratedLog_factorTwo_uniform_cutoff depth depthPositive eta etaPositive
  refine ⟨min costCutoff logCutoff, lt_min costPositive logPositive, ?_⟩
  intro delta exponent budget deltaPositive below small choice C retained accounting qualification
  have budgetCutoff : (budget : ℝ) < costCutoff :=
    choice.conservative.trans_lt (below.trans_le (min_le_left _ _))
  have logs := logBound delta (budget : ℝ) deltaPositive (below.trans_le (min_le_right _ _))
    choice.factor_two choice.conservative
  have idealBill := costBound budget choice.positive choice.small budgetCutoff C retained accounting
  obtain ⟨dominated, overflow, _quotas, native⟩ := truncation C retained accounting delta exponent budget
    deltaPositive small choice
  obtain ⟨policy, sameRule, _sameRun⟩ := native qualification
  have safe : risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta := by
    rw [← risk_uncapped_eq_native input C accounting policy.rule policy.legal, sameRule]
    calc
      _ ≤ risk input C .uncapped accounting (idealPolicy input C retained accounting budget).rule (Measure.dirac ()) +
          ENNReal.ofReal (delta/2) := overflow
      _ ≤ ENNReal.ofReal ((budget : ℝ)/2) + ENNReal.ofReal (delta/2) :=
        add_le_add (riskCost.1 C retained accounting budget choice.positive choice.small) le_rfl
      _ = ENNReal.ofReal ((budget : ℝ)/2 + delta/2) :=
        (ENNReal.ofReal_add (by exact div_nonneg (by exact_mod_cast choice.positive.le) (by norm_num)) (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [choice.conservative])
  have actualBill : expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
      expectedBill input C .uncapped accounting (idealPolicy input C retained accounting budget).rule (Measure.dirac ()) := by
    rw [← expectedBill_uncapped_eq_native input C accounting policy.rule policy.legal, sameRule]
    exact lintegral_mono dominated
  refine ⟨policy, sameRule, safe, ?_, value_le_policy_any_seed input C .native accounting policy (Measure.dirac ()) _ safe⟩
  apply actualBill.trans (idealBill.trans (ENNReal.ofReal_le_ofReal ?_))
  calc
    _ ≤ (1+eta)*headCoefficient input * ((1+eta)*iteratedLog depth (1/delta)) :=
      mul_le_mul_of_nonneg_left (by simpa only [one_div] using logs.2) (by positivity)
    _ = ((1+eta)*(1+eta))*headCoefficient input*iteratedLog depth (1/delta) := by ring
    _ ≤ _ := by
      simpa only [one_div] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right product coefficientPositive.le) logs.1.le

end PaperProofs.Retained.PRetNativeUpper121

