module

public import PaperProofs.Paid.PDMenu_SearchSolveFacts_130
public import PaperProofs.Paid.PDMenu_MajorityRisk_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchPenalty_le_majority (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) ≤
      ENNReal.ofReal ((P.B + P.Lambda * (P.certificate.risk / 2) : ℚ) : ℝ) := by
  have hB : 0 ≤ (P.B : ℝ) := by exact_mod_cast P.B_pos.le
  have hL : 0 ≤ (P.Lambda : ℝ) := by exact_mod_cast P.Lambda_pos.le
  have hd : 0 ≤ ((P.certificate.risk / 2 : ℚ) : ℝ) := by
    exact_mod_cast div_nonneg P.certificate.risk_pos.le (by norm_num : (0 : ℚ) ≤ 2)
  calc
    _ ≤ paidPenaltyObjective (P.input fee hfee) C.val accounting P.majorityRule (Measure.dirac ())
        (ENNReal.ofReal (P.Lambda : ℝ)) :=
      paidPenaltyValue_le_policy (P.input fee hfee) C.val accounting _ (Measure.dirac ()) (P.majorityPolicy fee hfee C accounting)
    _ ≤ ENNReal.ofReal (P.B : ℝ) + ENNReal.ofReal (P.Lambda : ℝ) * ENNReal.ofReal ((P.certificate.risk / 2 : ℚ) : ℝ) := by
      unfold paidPenaltyObjective
      rw [majority_expectedBill_eq_B]
      exact add_le_add le_rfl (mul_le_mul' le_rfl (majority_risk_le_half P fee hfee C accounting))
    _ = _ := by
      simp only [Rat.cast_add, Rat.cast_mul]
      rw [ENNReal.ofReal_add hB (mul_nonneg hL hd), ENNReal.ofReal_mul hL]

theorem searchUpper_objective_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    (P.solveRecord (P.solveMultiplier fee P.Lambda)).objective fee P.Lambda ≤
      P.B + P.Lambda * (P.certificate.risk / 2) := by
  have hsolve := searchSolveCorrect P fee hfee C accounting P.Lambda P.Lambda_pos.le le_rfl
  have hv : paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) =
      ENNReal.ofReal (((P.solveRecord (P.solveMultiplier fee P.Lambda)).objective fee P.Lambda : ℚ) : ℝ) := hsolve.2.2.2
  have h := searchPenalty_le_majority P fee hfee C accounting
  rw [hv] at h
  have hright : 0 ≤ ((P.B + P.Lambda * (P.certificate.risk / 2) : ℚ) : ℝ) := by
    exact_mod_cast add_nonneg P.B_pos.le (mul_nonneg P.Lambda_pos.le (div_nonneg P.certificate.risk_pos.le (by norm_num : (0 : ℚ) ≤ 2)))
  exact_mod_cast (ENNReal.ofReal_le_ofReal_iff hright).mp h

theorem searchUpper_risk_le_three_quarters (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.solveRisk (P.solveMultiplier fee P.Lambda) ≤ 3 * P.certificate.risk / 4 := by
  have ho := searchUpper_objective_le P fee hfee C accounting
  rw [searchSolve_objective] at ho
  have hc := (searchSolveStats P fee hfee P.Lambda).1
  have hr : P.solveRisk (P.solveMultiplier fee P.Lambda) ≤
      (P.B + P.Lambda * (P.certificate.risk / 2)) / P.Lambda :=
    (le_div_iff₀ P.Lambda_pos).mpr (by nlinarith)
  calc
    _ ≤ _ := hr
    _ = 3 * P.certificate.risk / 4 := by
      unfold PaperProofs.Paid.Parameters.Lambda
      field_simp [P.B_pos.ne', P.certificate.risk_pos.ne']
      ring

theorem searchUpper_risk_le_value_div (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val .uncapped accounting (P.solveRule (P.solveMultiplier fee P.Lambda))
      (menuSeedLaw P.certificate.stages P.tools) ≤
      paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) / ENNReal.ofReal (P.Lambda : ℝ) := by
  have hsolve := searchSolveCorrect P fee hfee C accounting P.Lambda P.Lambda_pos.le le_rfl
  have hv : paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) =
      ENNReal.ofReal (((P.solveRecord (P.solveMultiplier fee P.Lambda)).objective fee P.Lambda : ℚ) : ℝ) := hsolve.2.2.2
  have hL : 0 < (P.Lambda : ℝ) := by exact_mod_cast P.Lambda_pos
  rw [hsolve.2.2.1, hv, ← ENNReal.ofReal_div_of_pos hL]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hL).mpr
  rw [searchSolve_objective]
  have hc : 0 ≤ (P.solveCost fee (P.solveMultiplier fee P.Lambda) : ℝ) := by
    exact_mod_cast (searchSolveStats P fee hfee P.Lambda).1
  push_cast
  nlinarith

theorem searchUpper_value_div_le_baseline (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) / ENNReal.ofReal (P.Lambda : ℝ) ≤
      ENNReal.ofReal (((P.B / P.Lambda) + P.certificate.risk / 2 : ℚ) : ℝ) := by
  have hsolve := searchSolveCorrect P fee hfee C accounting P.Lambda P.Lambda_pos.le le_rfl
  have hv : paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) =
      ENNReal.ofReal (((P.solveRecord (P.solveMultiplier fee P.Lambda)).objective fee P.Lambda : ℚ) : ℝ) := hsolve.2.2.2
  have hL : 0 < (P.Lambda : ℝ) := by exact_mod_cast P.Lambda_pos
  have hr : (P.solveRecord (P.solveMultiplier fee P.Lambda)).objective fee P.Lambda / P.Lambda ≤
      P.B / P.Lambda + P.certificate.risk / 2 := by
    calc
      _ ≤ (P.B + P.Lambda * (P.certificate.risk / 2)) / P.Lambda :=
        div_le_div_of_nonneg_right (searchUpper_objective_le P fee hfee C accounting) P.Lambda_pos.le
      _ = _ := by field_simp [P.Lambda_pos.ne']
  rw [hv, ← ENNReal.ofReal_div_of_pos hL]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast hr

end PDMenu
