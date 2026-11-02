module

public import PaperProofs.Paid.PDMenu_SearchSolveFacts_130

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The original whole-policy paid penalty is a genuine lower bound for
the same original constrained actual-bill value, including infinite bills. -/
theorem searchPaidValue_sub_le_uncappedValue {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty budget : ℝ≥0∞) :
    paidPenaltyValue input C accounting penalty - penalty * budget ≤ value input C .uncapped accounting budget := by
  unfold value
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  apply tsub_le_iff_right.mpr
  exact (paidPenaltyValue_le_policy input C accounting penalty ν policy.val).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl policy.property))

theorem searchRecord_objective (P : Parameters) (fee : ℚ) (solution : MultiplierSolve) :
    (P.solveRecord solution).objective fee solution.multiplier =
      P.solveCost fee solution + solution.multiplier * P.solveRisk solution := rfl

theorem searchMixtureLower_le_value (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (upper : MultiplierSolve)
    (hsolve : P.SolveCorrect fee hfee C accounting upper) (hm : 0 ≤ upper.multiplier) :
    ENNReal.ofReal (P.mixtureLower fee upper : ℝ) ≤ P.uncappedValue C accounting fee hfee := by
  have hweak := searchPaidValue_sub_le_uncappedValue (P.input fee hfee) C.val accounting
    (ENNReal.ofReal (upper.multiplier : ℝ)) P.targetRisk
  rw [hsolve.2.2.2] at hweak
  have hmR : 0 ≤ (upper.multiplier : ℝ) := by exact_mod_cast hm
  have hdR : 0 ≤ (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos.le
  unfold PaperProofs.Paid.Parameters.mixtureLower
  rw [Rat.cast_sub, Rat.cast_mul, ENNReal.ofReal_sub _ (mul_nonneg hmR hdR), ENNReal.ofReal_mul hmR]
  exact hweak

def searchSolvePolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (solution : MultiplierSolve) :
    Policy (P.input fee hfee) C.val .uncapped accounting (MenuSeed P.certificate.stages P.tools) where
  rule := P.solveRule solution
  measurable_rule := P.measurable_compiledMenuRule P.certificate.stages P.tools solution.table
  legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools solution.table fee hfee C.val C.property.1.1 accounting

/-- Cross-optimality compares the two actual endpoint policies in the
original full policy infimum, with their original source multipliers. -/
theorem searchCrossObjective (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source candidate : MultiplierSolve)
    (hsource : P.SolveCorrect fee hfee C accounting source)
    (hcandidate : P.SolveCorrect fee hfee C accounting candidate)
    (hm : 0 ≤ source.multiplier) (hc : 0 ≤ P.solveCost fee candidate) (hr : 0 ≤ P.solveRisk candidate) :
    P.solveCost fee source + source.multiplier * P.solveRisk source ≤
      P.solveCost fee candidate + source.multiplier * P.solveRisk candidate := by
  have h := paidPenaltyValue_le_policy (P.input fee hfee) C.val accounting (ENNReal.ofReal (source.multiplier : ℝ))
    (menuSeedLaw P.certificate.stages P.tools) (searchSolvePolicy P fee hfee C accounting candidate)
  change paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (source.multiplier : ℝ)) ≤
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.solveRule candidate) (menuSeedLaw P.certificate.stages P.tools) +
      ENNReal.ofReal (source.multiplier : ℝ) *
        risk (P.input fee hfee) C.val .uncapped accounting (P.solveRule candidate) (menuSeedLaw P.certificate.stages P.tools) at h
  rw [hsource.2.2.2, hcandidate.2.1, hcandidate.2.2.1, searchRecord_objective] at h
  have hmR : 0 ≤ (source.multiplier : ℝ) := by exact_mod_cast hm
  have hcR : 0 ≤ (P.solveCost fee candidate : ℝ) := by exact_mod_cast hc
  have hrR : 0 ≤ (P.solveRisk candidate : ℝ) := by exact_mod_cast hr
  have hsum : ENNReal.ofReal (P.solveCost fee candidate : ℝ) +
      ENNReal.ofReal (source.multiplier : ℝ) * ENNReal.ofReal (P.solveRisk candidate : ℝ) =
      ENNReal.ofReal ((P.solveCost fee candidate + source.multiplier * P.solveRisk candidate : ℚ) : ℝ) := by
    simp only [Rat.cast_add, Rat.cast_mul]
    rw [ENNReal.ofReal_add hcR (mul_nonneg hmR hrR), ENNReal.ofReal_mul hmR]
  rw [hsum] at h
  have hright : 0 ≤ ((P.solveCost fee candidate + source.multiplier * P.solveRisk candidate : ℚ) : ℝ) := by
    exact_mod_cast add_nonneg hc (mul_nonneg hm hr)
  exact_mod_cast (ENNReal.ofReal_le_ofReal_iff hright).mp h

end PDMenu
