module

public import PaperProofs.Paid.PDMenu_FirstPositiveEvent_150

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped BigOperators ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem positiveStep_bill_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (tapes : ReviewTapes (P.input fee hfee)) {s next : State P.sharedInstance} {action : Action P.sharedInstance}
    (step : Step (P.input fee hfee) C.val mode accounting tapes s action next)
    (hpos : P.isPositiveVariableAction fee action = true) :
    ENNReal.ofReal (P.firstChargeFloor fee : ℝ) ≤ next.ledger.actualBill (P.input fee hfee).fees := by
  cases step with
  | review stage _ _ _ =>
      rw [record_actualBill]
      have hc : (1:ℕ∞) ≤ (reviewLedger s stage).reviews stage := by
        simp only [reviewLedger, Function.update_self]
        exact le_add_self
      have he : (1:ℝ≥0∞) ≤ ((reviewLedger s stage).reviews stage).toENNReal := by
        simpa only [ENat.toENNReal_one] using ENat.toENNReal_mono hc
      have hobs : ENNReal.ofReal (P.reviewFee:ℝ) ≤
          (reviewLedger s stage).observationBill (P.input fee hfee).fees := by
        calc
          _ = ENNReal.ofReal (((P.input fee hfee).fees.observation stage):ℝ) * 1 := by rw [mul_one]; rfl
          _ ≤ ENNReal.ofReal (((P.input fee hfee).fees.observation stage):ℝ) *
              ((reviewLedger s stage).reviews stage).toENNReal := mul_le_mul' le_rfl he
          _ ≤ _ := Finset.single_le_sum
            (f := fun i : P.sharedInstance.Stage => ENNReal.ofReal (((P.input fee hfee).fees.observation i):ℝ) *
              ((reviewLedger s stage).reviews i).toENNReal)
            (fun _ _ => bot_le) (Finset.mem_univ stage)
      exact (ENNReal.ofReal_le_ofReal (by exact_mod_cast
        PDROC.ZeroChargeLower.Transport.firstChargeFloor_le_reviewFee P fee)).trans
          (hobs.trans le_self_add)
  | execute handle tool _ _ _ _ _ _ _ _ =>
      have hfeePos : 0 < fee := by simpa only [Parameters.isPositiveVariableAction, decide_eq_true_eq] using hpos
      rw [record_actualBill, execute_actualBill]
      change ENNReal.ofReal (P.firstChargeFloor fee:ℝ) ≤ _ + ENNReal.ofReal (fee:ℝ)
      exact (ENNReal.ofReal_le_ofReal (by exact_mod_cast
        PDROC.ZeroChargeLower.Transport.firstChargeFloor_le_fee P fee hfeePos)).trans le_add_self
  | write | allocate | advance | stop | abandon =>
      simp only [Parameters.isPositiveVariableAction, Bool.false_eq_true] at hpos

/-- The first positive action is a genuine enabled original Step, hence
the source's complete all-path bill already pays the exact positive floor. -/
theorem positiveChargeEvent_pathfloor (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy (P.input fee hfee) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hfee).World)
    (hmem : sample ∈ P.positiveChargeEvent fee hfee C mode accounting policy.rule) :
    ENNReal.ofReal (P.firstChargeFloor fee:ℝ) ≤ runActualBill (P.input fee hfee) C.val mode accounting policy.rule sample := by
  obtain ⟨clock, ha, hpos⟩ := hmem
  have hp := run_prefix_of_active (P.input fee hfee) C.val mode accounting policy.rule policy.legal sample clock ha
  obtain ⟨next, step⟩ := policy.legal sample.1 _ _ clock _ hp ha
  have hnext := run_succ_of_step (P.input fee hfee) C.val mode accounting policy.rule sample clock next ha step
  have hf := positiveStep_bill_lower P fee hfee C mode accounting _ step hpos
  rw [← hnext] at hf
  exact hf.trans (le_iSup (fun n => (run (P.input fee hfee) C.val mode accounting policy.rule sample n).ledger.actualBill
    (P.input fee hfee).fees) (clock+1))

end PDMenu
