module

public import PaperProofs.Paid.PDMenu_MajorityRiskReduction_036
public import PaperProofs.Paid.PDMenu_MajorityActualBill_034
public import PaperProofs.Paid.PDLower_Majority_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

theorem majority_stage_error_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) :
    (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample : Unit × (P.input fee hfee).World |
        majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠ (P.input fee hfee).truthAt sample.2 stage} ≤
      ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) := by
  have ht : P.experiment.tapeLaw true {tape | majorityTapeDecision P tape ≠ true} ≤
      ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) :=
    PDLower.paid_majority_t0_tail P true
  have hf : P.experiment.tapeLaw false {tape | majorityTapeDecision P tape ≠ false} ≤
      ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) :=
    PDLower.paid_majority_t0_tail P false
  rw [majority_stage_error_eq]
  calc
    _ ≤ P.experiment.priorMass true * ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) +
        P.experiment.priorMass false * ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) := by
      gcongr
    _ = _ := by
      rw [← add_mul, show P.experiment.priorMass true + P.experiment.priorMass false = 1 by
        simpa only [Fintype.sum_bool] using P.experiment.priorMass_sum, one_mul]

theorem majority_risk_le_half (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) ≤
      ENNReal.ofReal ((P.certificate.risk / 2 : ℚ) : ℝ) := by
  have hStageCard : Fintype.card P.sharedInstance.Stage = P.certificate.stages :=
    (Fintype.card_fin P.sharedInstance.compatibility.length).trans P.stageCount_eq
  calc
    _ ≤ ∑ stage : P.sharedInstance.Stage, (P.input fee hfee).seededWorldLaw (Measure.dirac ())
        {sample : Unit × (P.input fee hfee).World |
          majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠
            (P.input fee hfee).truthAt sample.2 stage} := majority_risk_le_sum_stage_errors P fee hfee C accounting
    _ ≤ ∑ _stage : P.sharedInstance.Stage,
        ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) :=
      Finset.sum_le_sum (fun stage _ => majority_stage_error_le P fee hfee stage)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, hStageCard, nsmul_eq_mul]
      have hN : 0 < (P.certificate.stages : ℝ) := by exact_mod_cast P.certificate.stages_pos
      have hratio : (P.certificate.stages : ℝ) * (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) =
          ((P.certificate.risk / 2 : ℚ) : ℝ) := by
        push_cast
        field_simp [hN.ne']
      calc
        _ = ENNReal.ofReal ((P.certificate.stages : ℝ) * (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ = _ := congrArg ENNReal.ofReal hratio

/-- EXACT first four original MajorityInitialBracket witness fields. No
SolveCorrect, D16, native H0 or future multiplier-search property is assumed. -/
theorem majorityInitialBracket_baseline_fields (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    (∀ sample n, (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample n).ledger.executions = []) ∧
    (∀ sample, runActualBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample = ENNReal.ofReal (P.B : ℝ)) ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) = ENNReal.ofReal (P.B : ℝ) ∧
    risk (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) ≤
      ENNReal.ofReal ((P.certificate.risk / 2 : ℚ) : ℝ) :=
  ⟨majority_run_executions P fee hfee C accounting, majority_runActualBill_eq_B P fee hfee C accounting,
    majority_expectedBill_eq_B P fee hfee C accounting, majority_risk_le_half P fee hfee C accounting⟩

end PDMenu
