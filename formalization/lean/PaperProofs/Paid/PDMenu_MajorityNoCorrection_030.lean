module

public import PaperProofs.Paid.MultiplierSearch

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

theorem majorityCandidate_ne_execute (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (handle : MismatchHandle P.sharedInstance)
    (tool : P.sharedInstance.Tool) : P.majorityCandidateRule seed history ≠ .execute handle tool := by
  unfold majorityCandidateRule
  split
  · simp
  · split
    · dsimp only
      split
      · simp
      · split
        · split <;> simp
        · simp
    · split <;> simp

theorem majorityRule_ne_execute (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (handle : MismatchHandle P.sharedInstance)
    (tool : P.sharedInstance.Tool) : P.majorityRule seed history ≠ .execute handle tool := by
  unfold majorityRule searchGuardRule
  dsimp only
  split
  · exact majorityCandidate_ne_execute P seed history handle tool
  · simp

theorem majority_prefix_executions (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state) :
    state.ledger.executions = [] := by
  induction hp with
  | initial => rfl
  | @next n state next _ hs ih =>
    generalize ha : P.majorityRule seed state.history = action at hs
    cases hs with
    | execute handle tool => exact (majorityRule_ne_execute P seed state.history handle tool ha).elim
    | write =>
      classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | review | allocate | advance | stop | abandon => exact ih

theorem majority_run_executions (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World) (n : ℕ) :
    (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample n).ledger.executions = [] := by
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule
    (P.majorityPolicy fee hfee C accounting).legal sample n
  exact majority_prefix_executions P fee hfee C accounting sample.1 _ _ hp

theorem majority_runActualBill_eq_observation (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample =
      runObservationBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample := by
  unfold runActualBill runObservationBill
  apply iSup_congr
  intro n
  simp only [Ledger.actualBill, Ledger.correctionBill, majority_run_executions P fee hfee C accounting sample n,
    List.map_nil, List.sum_nil, add_zero]

end PDMenu
