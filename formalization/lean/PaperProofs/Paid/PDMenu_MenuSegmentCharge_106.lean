module

public import PaperProofs.Paid.PDMenu_MenuWrittenState_101
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

theorem menuReviewFrom_reviews_add (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) (target : I.Stage) :
    (menuReviewFrom input accounting stage start tape n).ledger.reviews target =
      start.ledger.reviews target + if target = stage then (n : ℕ∞) else 0 := by
  induction n with
  | zero => simp only [menuReviewFrom, Nat.cast_zero, ite_self, add_zero]
  | succ n ih =>
    by_cases he : target = stage
    · subst target
      simp only [menuReviewFrom, record, reviewLedger, Function.update_self, ih, ite_true,
        Nat.cast_add, Nat.cast_one, add_assoc]
    · simp only [menuReviewFrom, record, reviewLedger, Function.update_of_ne he, ih, ite_eq_right he, add_zero]

/-- Exact charge of actual review records, allowing infinite old counters
and retaining all old costs on paths that later fail or abandon. -/
theorem menuReviewFrom_observationBill (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) (fees : Fees I) :
    (menuReviewFrom input accounting stage start tape n).ledger.observationBill fees =
      start.ledger.observationBill fees + ENNReal.ofReal (fees.observation stage : ℝ) * n := by
  classical
  have hdelta : (∑ target : I.Stage, ENNReal.ofReal (fees.observation target : ℝ) *
      ((if target = stage then (n : ℕ∞) else 0 : ℕ∞) : ℝ≥0∞)) =
        ENNReal.ofReal (fees.observation stage : ℝ) * n := by
    simp only [apply_ite, ENat.toENNReal_coe, ENat.toENNReal_zero, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold Ledger.observationBill
  simp only [menuReviewFrom_reviews_add, ENat.toENNReal_add, mul_add, Finset.sum_add_distrib]
  rw [hdelta]

theorem menuReviewFrom_actualBill (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) (fees : Fees I) :
    (menuReviewFrom input accounting stage start tape n).ledger.actualBill fees =
      start.ledger.actualBill fees + ENNReal.ofReal (fees.observation stage : ℝ) * n := by
  have hcorrection : (menuReviewFrom input accounting stage start tape n).ledger.correctionBill fees =
      start.ledger.correctionBill fees := by
    unfold Ledger.correctionBill
    rw [menuReviewFrom_executions]
  unfold Ledger.actualBill
  rw [menuReviewFrom_observationBill, hcorrection]
  exact add_right_comm _ _ _

theorem menuWrittenFrom_actualBill (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (n : ℕ) (bit : Bool) (fees : Fees I) :
    (menuWrittenFrom input C accounting stage start tape n bit).ledger.actualBill fees =
      start.ledger.actualBill fees + ENNReal.ofReal (fees.observation stage : ℝ) * n := by
  unfold menuWrittenFrom
  rw [record_actualBill, reportedWrite_actualBill, menuReviewFrom_actualBill]

end PDMenu
