module

public import PaperProofs.Paid.PDMenu_MajorityTermination_033

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

theorem majority_runActualBill_eq_B (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample = ENNReal.ofReal (P.B : ℝ) := by
  rw [runActualBill_of_halted (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample
    (majorityActionBound P + 1) (majority_run_halts P fee hfee C accounting sample)]
  simp only [Ledger.actualBill, Ledger.correctionBill,
    majority_run_executions P fee hfee C accounting sample (majorityActionBound P + 1), List.map_nil, List.sum_nil, add_zero]
  have hcounts := majority_run_terminal_counts P fee hfee C accounting sample
  have hStageCard : Fintype.card P.sharedInstance.Stage = P.certificate.stages :=
    (Fintype.card_fin P.sharedInstance.compatibility.length).trans P.stageCount_eq
  have hsum :
      (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample
        (majorityActionBound P + 1)).ledger.observationBill (P.input fee hfee).fees =
      ∑ stage : P.sharedInstance.Stage,
        ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ) * (P.certificate.t0 : ℝ≥0∞) := by
    apply Finset.sum_congr rfl
    intro stage _
    simpa only [ENat.toENNReal_coe] using congrArg
      (fun count : ℕ∞ => ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ) * count.toENNReal)
      (hcounts stage)
  calc
    _ = ∑ stage : P.sharedInstance.Stage,
        ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ) * (P.certificate.t0 : ℝ≥0∞) := hsum
    _ = (P.certificate.stages : ℝ≥0∞) * (ENNReal.ofReal (P.reviewFee : ℝ) * (P.certificate.t0 : ℝ≥0∞)) := by
      simp only [StatisticalInput.fees, Parameters.input, Parameters.experiment,
        Finset.sum_const, Finset.card_univ, hStageCard, nsmul_eq_mul]
    _ = ENNReal.ofReal (P.B : ℝ) := by
      have hc : 0 ≤ (P.reviewFee : ℝ) := by exact_mod_cast P.reviewFee_pos.le
      rw [B, Rat.cast_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast,
        ENNReal.ofReal_mul (mul_nonneg hc (Nat.cast_nonneg _)), ENNReal.ofReal_mul hc]
      simp only [ENNReal.ofReal_natCast]
      ring

theorem majority_expectedBill_eq_B (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) = ENNReal.ofReal (P.B : ℝ) := by
  unfold expectedBill
  simp only [majority_runActualBill_eq_B P fee hfee C accounting, lintegral_const, measure_univ, mul_one]

/-- Exact first three original MajorityInitialBracket fields, without D16,
SolveCorrect, native H0, or any statement about a future bracket solver. -/
theorem majorityInitialBracket_cost_fields (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    (∀ sample n, (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample n).ledger.executions = []) ∧
    (∀ sample, runActualBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample = ENNReal.ofReal (P.B : ℝ)) ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) = ENNReal.ofReal (P.B : ℝ) :=
  ⟨majority_run_executions P fee hfee C accounting, majority_runActualBill_eq_B P fee hfee C accounting,
    majority_expectedBill_eq_B P fee hfee C accounting⟩

end PDMenu
