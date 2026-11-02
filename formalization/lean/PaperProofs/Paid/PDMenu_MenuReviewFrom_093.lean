module

public import PaperProofs.Paid.PDMenu_MenuReviewFrame_090

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

/-- Actual Native review records starting at an existing state. Every
record retains the original accounting and its complete past ledger. -/
def menuReviewFrom (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) : ℕ → State I
  | 0 => start
  | n + 1 =>
      let state := menuReviewFrom input accounting stage start tape n
      record accounting state (.review stage) [.observation stage (tape n).val]
        (reviewLedger state stage) state.cursor false

theorem menuReviewFrom_cursor (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).cursor = start.cursor := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem menuReviewFrom_active (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape)
    (hactive : start.halted = false) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).halted = false := by
  cases n with
  | zero => exact hactive
  | succ n => rfl

theorem menuReviewFrom_written (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).ledger.written = start.ledger.written := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem menuReviewFrom_reviews (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape)
    (hzero : start.ledger.reviews stage = 0) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).ledger.reviews stage = n := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    simp only [menuReviewFrom, record, reviewLedger, Function.update_self, ih, Nat.cast_add, Nat.cast_one]

theorem menuReviewFrom_history (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).history = start.history ++ headReviewHistory input stage tape n := by
  induction n with
  | zero => simp only [menuReviewFrom, headReviewHistory, List.ofFn_zero, List.append_nil]
  | succ n ih => simp only [menuReviewFrom, record, ih, headReviewHistory_succ, List.append_assoc]

/-- A pointwise review-prefix action identity yields the exact real
interpreter states from an arbitrary genuine earlier run state. No local
test performance or expected record is assumed. -/
theorem menu_run_eq_reviewFrom (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    (stage : I.Stage) (clock : ℕ) (start : State I)
    (hstart : run input C .uncapped accounting rule sample clock = start)
    (hactive : start.halted = false) (hcursor : start.cursor = stage.val)
    (hport : start.ledger.written stage = none) (hzero : start.ledger.reviews stage = 0)
    (steps : ℕ)
    (hprior : ∀ j < steps, rule sample.1
      (start.history ++ headReviewHistory input stage (worldTapes input sample.2 stage) j) = .review stage) :
    run input C .uncapped accounting rule sample (clock + steps) =
      menuReviewFrom input accounting stage start (worldTapes input sample.2 stage) steps := by
  revert hprior
  induction steps with
  | zero =>
    intro _
    simpa only [Nat.add_zero, menuReviewFrom] using hstart
  | succ steps ih =>
    intro hprior
    have hr := ih (fun j hj => hprior j (hj.trans (Nat.lt_succ_self steps)))
    let state := menuReviewFrom input accounting stage start (worldTapes input sample.2 stage) steps
    have ha : state.halted = false := menuReviewFrom_active input accounting stage start _ hactive steps
    have hc : state.cursor = stage.val := (menuReviewFrom_cursor input accounting stage start _ steps).trans hcursor
    have hw : state.ledger.written stage = none :=
      (congrFun (menuReviewFrom_written input accounting stage start _ steps) stage).trans hport
    have hcount : state.ledger.reviews stage = steps := menuReviewFrom_reviews input accounting stage start _ hzero steps
    have hs : Step input C .uncapped accounting (worldTapes input sample.2) state (.review stage)
        (menuReviewFrom input accounting stage start (worldTapes input sample.2 stage) (steps + 1)) := by
      have h := Step.review (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
        (tapes := worldTapes input sample.2) state stage ⟨ha, hc⟩ hw (.inl rfl)
      rw [menuReviewFrom]
      simpa only [hcount, ENat.toNat_natCast] using h
    rw [Nat.add_succ]
    apply run_succ_of_step input C .uncapped accounting rule sample (clock + steps) _
    · rw [hr]
      exact ha
    · rw [hr, menuReviewFrom_history, hprior steps (Nat.lt_succ_self steps)]
      exact hs

end PDMenu
