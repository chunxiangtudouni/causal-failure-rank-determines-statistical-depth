module

public import PaperProofs.Paid.PDMenu_MajorityControl_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

theorem majorityAtState_review_lt (P : Parameters) (state : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (h : majorityAtState P state = .review stage) :
    (state.ledger.reviews stage).toNat < P.certificate.t0 := by
  unfold majorityAtState at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
  · cases h

theorem majorityAtState_write_ge (P : Parameters) (state : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (bit : Bool) (h : majorityAtState P state = .write stage bit) :
    P.certificate.t0 ≤ (state.ledger.reviews stage).toNat := by
  unfold majorityAtState at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; omega
  · cases h

theorem majorityAtState_ne_abandon (P : Parameters) (state : State P.sharedInstance) :
    majorityAtState P state ≠ .abandon := by
  unfold majorityAtState
  split
  · dsimp only
    split
    · simp
    · split <;> simp
  · simp

theorem majorityAtState_stop_ge (P : Parameters) (state : State P.sharedInstance)
    (h : majorityAtState P state = .stop) : P.certificate.stages ≤ state.cursor := by
  unfold majorityAtState at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h <;> cases h
  · omega

private theorem majorityReportedWrite_reviews (P : Parameters) (C : Contract P.sharedInstance) (state : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (bit : Bool) :
    (reportedWriteLedger C state stage bit).reviews = state.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

private theorem majorityReportedWrite_written (P : Parameters) (C : Contract P.sharedInstance) (state : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (bit : Bool) :
    (reportedWriteLedger C state stage bit).written = Function.update state.ledger.written stage (some bit) := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

structure MajorityReviewInvariant (P : Parameters) (state : State P.sharedInstance) : Prop where
  review_le : ∀ stage, state.ledger.reviews stage ≤ (P.certificate.t0 : ℕ∞)
  written_count : ∀ stage, state.ledger.written stage ≠ none → state.ledger.reviews stage = (P.certificate.t0 : ℕ∞)

theorem majority_prefix_reviewInvariant (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state) :
    MajorityReviewInvariant P state := by
  induction hp with
  | initial =>
    exact ⟨fun _ => zero_le, fun _ hw => (hw rfl).elim⟩
  | @next n state next earlier hs ih =>
    have hactive := step_source_active (P.input fee hfee) C.val .uncapped accounting tapes hs
    have hcontrol := majorityRule_eq_atState P fee hfee C accounting seed truth tapes earlier hactive
    generalize ha : P.majorityRule seed state.history = action at hs
    cases hs with
    | review stage live port resources =>
      have hlt := majorityAtState_review_lt P state stage (hcontrol.symm.trans ha)
      have hfinite := prefix_reviews_natCast_toNat (P.input fee hfee) C.val .uncapped accounting
        P.majorityRule seed truth tapes earlier stage
      constructor
      · intro other
        by_cases he : other = stage
        · subst other
          simp only [record, reviewLedger, Function.update_self]
          rw [← hfinite]
          exact_mod_cast Nat.succ_le_of_lt hlt
        · simpa only [record, reviewLedger, Function.update_of_ne he] using ih.review_le other
      · intro other hw
        have hne : other ≠ stage := by
          intro he
          subst other
          exact hw port
        simpa only [record, reviewLedger, Function.update_of_ne hne] using ih.written_count other hw
    | write stage bit live port resources =>
      have hge := majorityAtState_write_ge P state stage bit (hcontrol.symm.trans ha)
      have hfinite := prefix_reviews_natCast_toNat (P.input fee hfee) C.val .uncapped accounting
        P.majorityRule seed truth tapes earlier stage
      have hle : (state.ledger.reviews stage).toNat ≤ P.certificate.t0 :=
        ENat.natCast_le_natCast.mp (by simpa only [hfinite] using ih.review_le stage)
      have hcount : state.ledger.reviews stage = (P.certificate.t0 : ℕ∞) :=
        hfinite.symm.trans (congrArg (fun value : ℕ => (value : ℕ∞)) (Nat.le_antisymm hle hge))
      constructor
      · intro other
        simpa only [record, majorityReportedWrite_reviews] using ih.review_le other
      · intro other hw
        have hsourceCount : state.ledger.reviews other = (P.certificate.t0 : ℕ∞) := by
          by_cases he : other = stage
          · subst other; exact hcount
          · exact ih.written_count other (by
              simpa only [record, majorityReportedWrite_written, Function.update_of_ne he] using hw)
        simpa only [record, majorityReportedWrite_reviews] using hsourceCount
    | allocate | execute | advance | stop | abandon => exact ⟨ih.review_le, ih.written_count⟩

theorem majority_prefix_behind_written (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state) :
    ∀ stage, stage.val < state.cursor → state.ledger.written stage ≠ none := by
  induction hp with
  | initial =>
    intro stage hs
    have hfalse : stage.val < 0 := hs
    omega
  | @next n state next earlier hs ih =>
    generalize ha : P.majorityRule seed state.history = action at hs
    cases hs with
    | write stage bit live port resources =>
      intro other hother
      change other.val < state.cursor at hother
      have hne : other ≠ stage := by intro he; subst other; have hc := live.2; omega
      simpa only [record, majorityReportedWrite_written, Function.update_of_ne hne] using ih other hother
    | advance stage live written resources =>
      intro other hother
      by_cases hbefore : other.val < state.cursor
      · exact ih other hbefore
      · have heq : other = stage := Fin.ext (by have hc := live.2; change other.val < state.cursor + 1 at hother; omega)
        subst other
        exact written
    | review | allocate | execute | stop | abandon => exact ih

theorem majority_prefix_halted_cursor (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state)
    (hh : state.halted = true) : state.cursor = P.certificate.stages := by
  cases hp with
  | initial => cases hh
  | @next n source next earlier hs =>
    have hactive := step_source_active (P.input fee hfee) C.val .uncapped accounting tapes hs
    have hcontrol := majorityRule_eq_atState P fee hfee C accounting seed truth tapes earlier hactive
    generalize ha : P.majorityRule seed source.history = action at hs
    cases hs with
    | stop =>
      have hge := majorityAtState_stop_ge P source (hcontrol.symm.trans ha)
      have hb := (prefix_cursorInvariant (P.input fee hfee) C.val .uncapped accounting
        P.majorityRule seed truth tapes earlier).bound
      rw [P.stageCount_eq] at hb
      change source.cursor = P.certificate.stages
      omega
    | abandon => exact (majorityAtState_ne_abandon P source (hcontrol.symm.trans ha)).elim
    | review | write | allocate | execute | advance => cases hh

end PDMenu
