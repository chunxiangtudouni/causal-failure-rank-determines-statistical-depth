module

public import PaperProofs.Paid.PDMenu_MenuEndpointRun_095
public import PaperProofs.Paid.PDMenu_MenuHistoryPermissions_066

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem menuReviewFrom_truth (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).ledger.truth = start.ledger.truth := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem menuReviewFrom_commitments (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).ledger.commitments = start.ledger.commitments := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem menuReviewFrom_executions (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).ledger.executions = start.ledger.executions := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem menuReviewFrom_clock (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (menuReviewFrom input accounting stage start tape n).clock = start.clock + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (menuReviewFrom input accounting stage start tape n).clock + 1 = start.clock + (n + 1)
    rw [ih, Nat.add_assoc]

theorem menuWrittenFrom_fields (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) :
    let state := menuWrittenFrom input C accounting stage start tape reviews bit
    state.cursor = start.cursor ∧ state.halted = false ∧ state.clock = start.clock + reviews + 1 ∧
      state.ledger.truth = start.ledger.truth ∧ state.ledger.commitments = start.ledger.commitments ∧
        state.ledger.executions = start.ledger.executions ∧ state.ledger.written stage = some bit := by
  classical
  refine ⟨menuReviewFrom_cursor input accounting stage start tape reviews, rfl,
    congrArg (fun n : ℕ => n + 1) (menuReviewFrom_clock input accounting stage start tape reviews), ?_⟩
  simp only [menuWrittenFrom, record, reportedWriteLedger]
  split_ifs <;> exact ⟨menuReviewFrom_truth input accounting stage start tape reviews,
    menuReviewFrom_commitments input accounting stage start tape reviews,
    menuReviewFrom_executions input accounting stage start tape reviews, by simp only [writeLedger, Function.update_self]⟩

theorem menuReviewFrom_used (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    historyUsed (menuReviewFrom input accounting stage start tape n).history = historyUsed start.history := by
  rw [menuReviewFrom_history]
  unfold historyUsed historyCommitments
  rw [List.filterMap_append, menuReviewPacket_filterMap_none input stage tape n eventCommitment (by intro; rfl), List.append_nil]

theorem menuWrittenFrom_used (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) :
    historyUsed (menuWrittenFrom input C accounting stage start tape reviews bit).history = historyUsed start.history := by
  let state := menuReviewFrom input accounting stage start tape reviews
  have hw : historyUsed (state.history ++ writeResponses C state stage bit) = historyUsed state.history := by
    simp only [historyUsed, historyCommitments, List.filterMap_append, writeResponses, hearly, ite_true,
      List.filterMap_cons, List.filterMap_nil, eventCommitment, List.append_nil]
  exact hw.trans (menuReviewFrom_used input accounting stage start tape reviews)

theorem menuWrittenFrom_entryTools (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (stage : (freshInstance N K).Stage)
    (start : State (freshInstance N K)) (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (reviews : ℕ) (bit : Bool) :
    P.menuEntryTools N K (menuWrittenFrom (P.freshInput N K fee hfee) C accounting stage start tape reviews bit).history stage =
      P.menuEntryTools N K start.history stage := by
  change P.menuEntryTools N K
    ((menuReviewFrom (P.freshInput N K fee hfee) accounting stage start tape reviews).history ++
      writeResponses C (menuReviewFrom (P.freshInput N K fee hfee) accounting stage start tape reviews) stage bit) stage = _
  rw [menuEntryTools_append_writeResponses P N K C hearly, menuReviewFrom_history, menuReviewFrame_entryTools]

/-- No new commitment is invented by a review/write segment. The actual
entry's empty port rules out a hidden earlier commitment on this stage. -/
theorem menuWrittenFrom_no_current_commitment (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {clock : ℕ} {start : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes clock start)
    (stage : I.Stage) (hport : start.ledger.written stage = none)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) :
    ∀ commitment ∈ (menuWrittenFrom input C accounting stage start tape reviews bit).ledger.commitments,
      commitment.handle.stage ≠ stage := by
  have hcommit := (menuWrittenFrom_fields input C accounting stage start tape reviews bit).2.2.2.2.1
  have hinv := prefix_invariant input C .uncapped accounting rule seed truth tapes hp
  intro commitment hc hs
  rw [hcommit] at hc
  have hg := (hinv.commitment_genuine commitment hc).1
  rw [hs, hport] at hg
  cases hg

end PDMenu
