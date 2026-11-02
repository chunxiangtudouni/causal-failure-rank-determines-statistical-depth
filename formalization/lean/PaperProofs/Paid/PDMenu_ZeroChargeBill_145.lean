module

public import PaperProofs.Paid.PDMenu_ZeroChargeNoPositive_144

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem zeroCharge_step_free (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (tapes : ReviewTapes (P.input fee hfee)) {s next : State P.sharedInstance} {action : Action P.sharedInstance}
    (step : Step (P.input fee hfee) C.val mode accounting tapes s action next)
    (hno : P.isPositiveVariableAction fee action = false) :
    next.ledger.actualBill (P.input fee hfee).fees = s.ledger.actualBill (P.input fee hfee).fees ∧
      ∀ stage, next.ledger.reviews stage = s.ledger.reviews stage := by
  cases step with
  | review => simp only [Parameters.isPositiveVariableAction, Bool.true_eq_false] at hno
  | write =>
      constructor
      · simp only [record_actualBill, reportedWrite_actualBill]
      · intro stage
        simp only [record, reportedWriteLedger, C.property.1.1, ite_true, writeLedger]
  | allocate handle tool _ _ _ _ _ _ _ =>
      exact ⟨allocate_actualBill s handle tool (P.input fee hfee).fees, fun _ => rfl⟩
  | execute handle tool _ _ _ _ _ _ _ _ =>
      have hfee0 : fee = 0 := le_antisymm (by simpa only [Parameters.isPositiveVariableAction,
        decide_eq_false_iff_not, not_lt] using hno) hfee
      constructor
      · simp only [record_actualBill, execute_actualBill]
        change _ + ENNReal.ofReal (fee : ℝ) = _
        simp only [hfee0, Rat.cast_zero, ENNReal.ofReal_zero, add_zero]
      · intro stage; rfl
  | advance stage _ _ _ => exact ⟨advance_actualBill s stage (P.input fee hfee).fees, fun _ => rfl⟩
  | stop => exact ⟨stop_actualBill s false (P.input fee hfee).fees, fun _ => rfl⟩
  | abandon => exact ⟨stop_actualBill s true (P.input fee hfee).fees, fun _ => rfl⟩

/-- Zero spending and zero reviews at every genuine prefix. This retains
all failed and nonreturning prefixes and assumes no expected-cost bound. -/
theorem zeroCharge_prefix_free (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (seed : MenuSeed P.certificate.stages P.tools) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val mode accounting (P.zeroChargeRule fee) seed truth tapes clock state) :
    state.ledger.actualBill (P.input fee hfee).fees = 0 ∧ ∀ stage, state.ledger.reviews stage = 0 := by
  induction hp with
  | initial => exact ⟨initial_actualBill _ _, fun _ => rfl⟩
  | @next n s next earlier step ih =>
      have hno := zeroChargeRule_noPositive P fee seed s.history
      have hf := zeroCharge_step_free P fee hfee C mode accounting tapes step hno
      exact ⟨hf.1.trans ih.1, fun stage => (hf.2 stage).trans (ih.2 stage)⟩

theorem zeroCharge_run_free (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World) (clock : ℕ) :
    (run (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample clock).ledger.actualBill (P.input fee hfee).fees = 0 ∧
      ∀ stage, (run (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample clock).ledger.reviews stage = 0 := by
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee)
    (P.zeroChargePolicy fee hfee C accounting).legal sample clock
  exact zeroCharge_prefix_free P fee hfee C .uncapped accounting sample.1 _ _ hp

theorem zeroCharge_runActualBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample = 0 := by
  apply le_antisymm ?_ bot_le
  exact iSup_le (fun clock => (zeroCharge_run_free P fee hfee C accounting sample clock).1.le)

theorem zeroCharge_expectedBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee)
      (menuSeedLaw P.certificate.stages P.tools) = 0 := by
  simp only [expectedBill, zeroCharge_runActualBill P fee hfee C accounting, MeasureTheory.lintegral_zero]

end PDMenu
