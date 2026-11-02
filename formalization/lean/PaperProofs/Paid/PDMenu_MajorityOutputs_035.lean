module

public import PaperProofs.Paid.PDMenu_MajorityTermination_033
public import PaperProofs.Common.ReferenceMassFlow
public import PaperProofs.Common.HistorySuffixSuccess

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

def majorityTapeDecision (P : Parameters) (tape : P.experiment.Tape) : Bool :=
  decide (0 ≤ menuWordScore (List.ofFn (fun i : Fin P.certificate.t0 => (tape i.val).val)))

theorem majorityAtState_write_decision (P : Parameters) (state : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (bit : Bool) (h : majorityAtState P state = .write stage bit) :
    bit = decide (0 ≤ menuWordScore (historyObservations state.history stage)) := by
  unfold majorityAtState at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl
  · cases h

theorem majority_write_count (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state)
    (ha : state.halted = false) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hwrite : P.majorityRule seed state.history = .write stage bit) :
    state.ledger.reviews stage = (P.certificate.t0 : ℕ∞) := by
  have hcontrol := majorityRule_eq_atState P fee hfee C accounting seed truth tapes hp ha
  have hge := majorityAtState_write_ge P state stage bit (hcontrol.symm.trans hwrite)
  have hfinite := prefix_reviews_natCast_toNat (P.input fee hfee) C.val .uncapped accounting
    P.majorityRule seed truth tapes hp stage
  have hle : (state.ledger.reviews stage).toNat ≤ P.certificate.t0 :=
    ENat.natCast_le_natCast.mp (by simpa only [hfinite] using
      (majority_prefix_reviewInvariant P fee hfee C accounting seed truth tapes hp).review_le stage)
  exact hfinite.symm.trans (congrArg (fun value : ℕ => (value : ℕ∞)) (Nat.le_antisymm hle hge))

/-- Every output bit found in any actual prefix comes from the literal
original t0-majority word, even on an eventual-failure path. -/
theorem majority_prefix_written_decision (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state)
    (stage : P.sharedInstance.Stage) (bit : Bool) (hw : state.ledger.written stage = some bit) :
    bit = majorityTapeDecision P (tapes stage) := by
  obtain ⟨_, old, _, hpOld, haOld, hwrite⟩ := prefix_written_has_write (P.input fee hfee) C.val
    .uncapped accounting P.majorityRule seed truth tapes hp stage bit hw
  have hcontrol := majorityRule_eq_atState P fee hfee C accounting seed truth tapes hpOld haOld
  have hdecision := majorityAtState_write_decision P old stage bit (hcontrol.symm.trans hwrite)
  have hcount := majority_write_count P fee hfee C accounting seed truth tapes hpOld haOld stage bit hwrite
  have hnat : (old.ledger.reviews stage).toNat = P.certificate.t0 := by rw [hcount, ENat.toNat_natCast]
  have hword := prefix_historyObservations_eq_tapeWord (P.input fee hfee) C.val .uncapped accounting
    P.majorityRule seed truth tapes hpOld stage
  rw [hnat] at hword
  simpa only [majorityTapeDecision, hword] using hdecision

theorem majority_runSuccess_of_all_correct (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World)
    (hall : ∀ stage, majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) =
      (P.input fee hfee).truthAt sample.2 stage) :
    runSuccess (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample := by
  let clock := majorityActionBound P + 1
  let final := run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample clock
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule
    (P.majorityPolicy fee hfee C accounting).legal sample clock
  have hh : final.halted = true := majority_run_halts P fee hfee C accounting sample
  have hcursor : final.cursor = P.certificate.stages := majority_prefix_halted_cursor P fee hfee C accounting
    sample.1 _ _ hp hh
  have hnotAbandoned : final.ledger.abandoned = false := majority_prefix_not_abandoned P fee hfee C accounting
    sample.1 _ _ hp
  have hwritten : allWritten final.ledger := by
    intro stage
    apply majority_prefix_behind_written P fee hfee C accounting sample.1 _ _ hp stage
    rw [hcursor]
    simpa [sharedInstance] using stage.isLt
  have hfinished := prefix_halted_allWritten_finished (P.input fee hfee) C.val .uncapped accounting
    P.majorityRule sample.1 _ _ hp hh hwritten
  have hcorrect (stage : P.sharedInstance.Stage) : final.ledger.written stage = some (final.ledger.truth stage) := by
    cases hw : final.ledger.written stage with
    | none => exact (hwritten stage hw).elim
    | some bit =>
      have hbit := majority_prefix_written_decision P fee hfee C accounting sample.1 _ _ hp stage bit hw
      have htruth := congrFun (run_truth (P.input fee hfee) C.val .uncapped accounting P.majorityRule
        (P.majorityPolicy fee hfee C accounting).legal sample clock) stage
      exact congrArg some (hbit.trans ((hall stage).trans htruth.symm))
  refine ⟨clock, hh, ?_⟩
  apply (prefix_success_iff_physical (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample.1 _ _ hp).mpr
  exact ⟨hfinished, hnotAbandoned, fun stage => (finalOutput_correct_iff final.ledger stage).mpr (.inl (hcorrect stage))⟩

theorem majority_failure_subset (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    {sample : Unit × (P.input fee hfee).World | ¬ runSuccess (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample} ⊆
      ⋃ stage : P.sharedInstance.Stage, {sample : Unit × (P.input fee hfee).World |
        majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠ (P.input fee hfee).truthAt sample.2 stage} := by
  classical
  intro sample hfailure
  have hnot : ¬ ∀ stage, majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) =
      (P.input fee hfee).truthAt sample.2 stage := by
    intro hall
    exact hfailure (majority_runSuccess_of_all_correct P fee hfee C accounting sample hall)
  obtain ⟨stage, hwrong⟩ := not_forall.mp hnot
  exact Set.mem_iUnion.mpr ⟨stage, hwrong⟩

end PDMenu
