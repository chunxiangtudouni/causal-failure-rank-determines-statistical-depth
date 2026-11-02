module

public import PaperProofs.Paid.PDMenu_PaidIndependentUpper_043
public import PaperProofs.Paid.PDMenu_FreshSuffixPolicies_041
public import PaperProofs.Paid.PDMenu_PaidUpperAlgebra_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

/-- A real endpoint test and epsilon-near true good continuation, followed by
actual abandonment on a bad head, give this full-policy upper bound. -/
theorem freshPaidPenalty_noRepair_endpoint_upper (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k m : ℕ) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤) :
    P.freshPaidPenalty fee hfee (n + 1) k penalty ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
        ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) * P.freshPaidPenalty fee hfee n k penalty +
        ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) * penalty := by
  apply bellman_le_of_forall_real_epsilon
  intro epsilon hepsilon
  obtain ⟨Seed, mSeed, seedRest⟩ := exists_paidPenaltyObjective_near
    (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty hp epsilon hepsilon
  let : MeasurableSpace Seed := mSeed
  obtain ⟨ν, hν, source, hnear⟩ := seedRest
  let : IsProbabilityMeasure ν := hν
  let head : (freshInstance (n + 1) k).Stage := ⟨0, by simp [freshInstance]⟩
  let charge := ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ)
  let correct := ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ))
  let wrong := ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)
  let childCost := paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _)
    (zeroAccounting _) source.rule ν penalty
  have hbound : P.freshPaidPenalty fee hfee (n + 1) k penalty ≤
      charge + correct * childCost + wrong * penalty := by
    have h := paidIndependentPolicy_noTool_upper (P.freshInput (n + 1) k fee hfee) head rfl
      fairGuessLaw ν (freshEndpointTest P (n + 1) k fee hfee head m) Finset.univ
      (freshGoodSuffixPolicy P fee hfee n k source) penalty
    rw [freshEndpointTest_bayesCharge, freshEndpointTest_correctMass,
      freshEndpointTest_bayesError, freshGoodSuffixPolicy_objective] at h
    change P.freshPaidPenalty fee hfee (n + 1) k penalty ≤ charge + (correct * childCost + wrong * penalty) at h
    simpa only [add_assoc] using h
  calc
    _ ≤ charge + correct * childCost + wrong * penalty := hbound
    _ ≤ charge + correct * (P.freshPaidPenalty fee hfee n k penalty + ENNReal.ofReal epsilon) +
        wrong * (penalty + ENNReal.ofReal epsilon) := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_right hnear.le correct))
        (mul_le_mul_right (le_self_add : penalty ≤ penalty + ENNReal.ofReal epsilon) wrong)
    _ = _ := paidWeightedNear_sum charge (P.freshPaidPenalty fee hfee n k penalty) penalty correct wrong
      (ENNReal.ofReal epsilon) (freshEndpoint_weights_sum P (n + 1) k fee hfee head m)

/-- A real correction at the head plus an independently sampled genuine
near-optimal k-tool continuation gives the correction alternative. -/
theorem freshPaidPenalty_repair_endpoint_upper (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k m : ℕ) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤) :
    P.freshPaidPenalty fee hfee (n + 1) (k + 1) penalty ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
        ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) * P.freshPaidPenalty fee hfee n (k + 1) penalty +
        ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) *
          (ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty) := by
  apply bellman_le_of_forall_real_epsilon
  intro epsilon hepsilon
  obtain ⟨Good, mGood, goodRest⟩ := exists_paidPenaltyObjective_near
    (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty hp epsilon hepsilon
  let : MeasurableSpace Good := mGood
  obtain ⟨goodLaw, hGood, goodSource, hgood⟩ := goodRest
  let : IsProbabilityMeasure goodLaw := hGood
  obtain ⟨Bad, mBad, badRest⟩ := exists_paidPenaltyObjective_near
    (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty hp epsilon hepsilon
  let : MeasurableSpace Bad := mBad
  obtain ⟨badLaw, hBad, badSource, hbad⟩ := badRest
  let : IsProbabilityMeasure badLaw := hBad
  let input := P.freshInput (n + 1) (k + 1) fee hfee
  let head : (freshInstance (n + 1) (k + 1)).Stage := ⟨0, by simp [freshInstance]⟩
  let charge := ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ)
  let correct := ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ))
  let wrong := ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)
  let good := freshGoodSuffixPolicy P fee hfee n (k + 1) goodSource
  let bad := freshBadSuffixPolicy P fee hfee n k badSource
  let goodCost := paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
    good.val.rule goodLaw penalty
  let badCost := paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
    bad.val.rule badLaw penalty
  have hgoodCost : goodCost ≤ P.freshPaidPenalty fee hfee n (k + 1) penalty + ENNReal.ofReal epsilon := by
    exact (freshGoodSuffixPolicy_objective P fee hfee n (k + 1) goodSource goodLaw penalty).le.trans hgood.le
  have hbadCost : badCost ≤ P.freshPaidPenalty fee hfee n k penalty + ENNReal.ofReal epsilon :=
    (freshBadSuffixPolicy_objective_le P fee hfee n k badSource badLaw penalty).trans hbad.le
  have hbound : P.freshPaidPenalty fee hfee (n + 1) (k + 1) penalty ≤
      charge + correct * goodCost + wrong * (ENNReal.ofReal (fee : ℝ) + badCost) := by
    have h := paidIndependentPolicy_someTool_upper input head rfl fairGuessLaw goodLaw badLaw
      (freshEndpointTest P (n + 1) (k + 1) fee hfee head m) Finset.univ (Fin.last k)
      (Finset.mem_univ _) (by simp [head, freshInstance, Instance.eligible]; exact Finset.mem_univ _) good bad penalty
    dsimp only [input] at h
    rw [freshEndpointTest_bayesCharge, freshEndpointTest_correctMass, freshEndpointTest_bayesError] at h
    change P.freshPaidPenalty fee hfee (n + 1) (k + 1) penalty ≤
      charge + (correct * goodCost + wrong * (ENNReal.ofReal (fee : ℝ) + badCost)) at h
    simpa only [add_assoc] using h
  calc
    _ ≤ charge + correct * goodCost + wrong * (ENNReal.ofReal (fee : ℝ) + badCost) := hbound
    _ ≤ charge + correct * (P.freshPaidPenalty fee hfee n (k + 1) penalty + ENNReal.ofReal epsilon) +
        wrong * ((ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty) + ENNReal.ofReal epsilon) := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_right hgoodCost correct))
        (mul_le_mul_right (by simpa only [add_assoc] using add_le_add le_rfl hbadCost) wrong)
    _ = _ := paidWeightedNear_sum charge (P.freshPaidPenalty fee hfee n (k + 1) penalty)
      (ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty) correct wrong
      (ENNReal.ofReal epsilon) (freshEndpoint_weights_sum P (n + 1) (k + 1) fee hfee head m)

end PDMenu



