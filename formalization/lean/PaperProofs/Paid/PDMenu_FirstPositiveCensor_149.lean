module

public import PaperProofs.Paid.PDMenu_ZeroChargeBill_145

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def firstPositiveCensorRule (P : Parameters) (fee : ℚ) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) : PolicyRule P.sharedInstance Seed :=
  fun seed history =>
    if P.isPositiveVariableAction fee (rule seed history) then .abandon else rule seed history

theorem firstPositiveCensor_prefix_active (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee rule)
      seed truth tapes clock state) :
    state.halted = false → Prefix (P.input fee hfee) C.val mode accounting rule seed truth tapes clock state := by
  induction hp with
  | initial => intro _; exact .initial
  | @next n s next earlier step ih =>
      intro ha
      have hpold := ih (step_source_active (P.input fee hfee) C.val mode accounting tapes step)
      by_cases hpos : P.isPositiveVariableAction fee (rule seed s.history) = true
      · have hac : firstPositiveCensorRule P fee rule seed s.history = .abandon := by
          simp only [firstPositiveCensorRule, hpos, ite_true]
        rw [hac] at step
        cases step
        simp only [stopState, Bool.true_eq_false] at ha
      · apply Prefix.next hpold
        simpa only [firstPositiveCensorRule, ite_eq_right hpos] using step

def firstPositiveCensorPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) :
    Policy (P.input fee hfee) C.val mode accounting Seed where
  rule := firstPositiveCensorRule P fee policy.rule
  measurable_rule := by
    simpa only [MeasurableRule, firstPositiveCensorRule, Function.comp_def] using
      (measurable_of_countable (fun action : Action P.sharedInstance =>
        if P.isPositiveVariableAction fee action then (Action.abandon : Action P.sharedInstance) else action)).comp policy.measurable_rule
  legal := by
    intro seed truth tapes n s hp ha
    have hpold := firstPositiveCensor_prefix_active P fee hfee C mode accounting policy.rule seed truth tapes hp ha
    by_cases hpos : P.isPositiveVariableAction fee (policy.rule seed s.history) = true
    · refine ⟨stopState s true, ?_⟩
      simpa only [firstPositiveCensorRule, hpos, ite_true] using
        (Step.abandon (input := P.input fee hfee) (C := C.val) (mode := mode)
          (accounting := accounting) (tapes := tapes) s ha)
    · obtain ⟨next, step⟩ := policy.legal seed truth tapes n s hpold ha
      exact ⟨next, by simpa only [firstPositiveCensorRule, ite_eq_right hpos] using step⟩

theorem firstPositiveCensor_noPositive (P : Parameters) (fee : ℚ) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed) (history : List (VisibleEvent P.sharedInstance)) :
    P.isPositiveVariableAction fee (firstPositiveCensorRule P fee rule seed history) = false := by
  by_cases hp : P.isPositiveVariableAction fee (rule seed history) = true
  · unfold firstPositiveCensorRule
    rw [ite_eq_left hp]
    rfl
  · unfold firstPositiveCensorRule
    rw [ite_eq_right hp]
    exact Bool.eq_false_iff.mpr hp

theorem noPositive_prefix_free (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} (rule : PolicyRule P.sharedInstance Seed)
    (hno : ∀ seed history, P.isPositiveVariableAction fee (rule seed history) = false)
    (seed : Seed) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val mode accounting rule seed truth tapes clock state) :
    state.ledger.actualBill (P.input fee hfee).fees = 0 := by
  induction hp with
  | initial => exact initial_actualBill _ _
  | @next n s next earlier step ih =>
      exact (zeroCharge_step_free P fee hfee C mode accounting tapes step (hno seed s.history)).1.trans ih

theorem firstPositiveCensor_runActualBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee policy.rule) sample = 0 := by
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro clock
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val mode accounting
    (firstPositiveCensorRule P fee policy.rule) (firstPositiveCensorPolicy P fee hfee C mode accounting policy).legal sample clock
  exact (noPositive_prefix_free P fee hfee C mode accounting (firstPositiveCensorRule P fee policy.rule)
    (firstPositiveCensor_noPositive P fee policy.rule) sample.1 _ _ hp).le

theorem firstPositiveCensor_expectedBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    expectedBill (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee policy.rule) ν = 0 := by
  simp only [expectedBill, firstPositiveCensor_runActualBill P fee hfee C mode accounting policy, lintegral_zero]

end PDMenu
