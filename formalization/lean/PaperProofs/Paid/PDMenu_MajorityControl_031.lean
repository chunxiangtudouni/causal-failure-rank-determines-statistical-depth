module

public import PaperProofs.Paid.PDMenu_MajorityNoCorrection_030
public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006
public import PaperProofs.Common.NativeObservedWords
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

/-- Analysis-only description of the actual majority action. No hidden
truth, next response, risk or cost guarantee is an input to the controller. -/
def majorityAtState (P : Parameters) (state : State P.sharedInstance) : Action P.sharedInstance :=
  if hstage : state.cursor < P.certificate.stages then
    let stage : P.sharedInstance.Stage := ⟨state.cursor, by simpa [sharedInstance] using hstage⟩
    match state.ledger.written stage with
    | some _ => .advance stage
    | none => if (state.ledger.reviews stage).toNat < P.certificate.t0 then .review stage
      else .write stage (decide (0 ≤ menuWordScore (historyObservations state.history stage)))
  else .stop

theorem majorityCandidate_eq_atState (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state)
    (ha : state.halted = false) : P.majorityCandidateRule seed state.history = majorityAtState P state := by
  have hcursor := prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp
  have hhalt := prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp
  simp only [majorityCandidateRule, majorityAtState, hhalt, ha, Bool.false_eq_true, ite_false, hcursor]
  split
  next hstage =>
    let stage : P.sharedInstance.Stage := ⟨state.cursor, by simpa [sharedInstance] using hstage⟩
    change (match historyWrite state.history stage with
      | some _ => Action.advance stage
      | none => if (historyObservations state.history stage).all (fun symbol => symbol < 2) then
          if (historyObservations state.history stage).length < P.certificate.t0 then Action.review stage
          else Action.write stage (decide (0 ≤ menuWordScore (historyObservations state.history stage)))
        else Action.abandon) =
      (match state.ledger.written stage with
      | some _ => Action.advance stage
      | none => if (state.ledger.reviews stage).toNat < P.certificate.t0 then Action.review stage
        else Action.write stage (decide (0 ≤ menuWordScore (historyObservations state.history stage))))
    have hvalid : (historyObservations state.history stage).all (fun symbol => symbol < 2) = true := by
      apply List.all_eq_true.mpr
      intro symbol hm
      simp only [decide_eq_true_eq]
      exact prefix_historyObservation_alphabet (P.input fee hfee) C.val .uncapped accounting
        P.majorityRule seed truth tapes hp stage symbol hm
    rw [prefix_historyWrite (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp stage]
    cases hw : state.ledger.written stage with
    | none =>
      simp only [Option.map_none, hvalid, ite_true,
        prefix_historyObservations_length_toNat (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp stage]
    | some bit => simp only [Option.map_some]
  next hstage =>
    have hb := (prefix_cursorInvariant (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp).bound
    have heq : state.cursor = P.certificate.stages := by
      rw [P.stageCount_eq] at hb
      omega
    simp only [heq, ite_true]

theorem majorityAtState_step (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (tapes : ReviewTapes (P.input fee hfee))
    (state : State P.sharedInstance) (ha : state.halted = false) :
    ∃ next, Step (P.input fee hfee) C.val .uncapped accounting tapes state (majorityAtState P state) next := by
  by_cases hstage : state.cursor < P.certificate.stages
  · let stage : P.sharedInstance.Stage := ⟨state.cursor, by simpa [sharedInstance] using hstage⟩
    simp only [majorityAtState, hstage, dite_true]
    change ∃ next, Step (P.input fee hfee) C.val .uncapped accounting tapes state
      (match state.ledger.written stage with
      | some _ => .advance stage
      | none => if (state.ledger.reviews stage).toNat < P.certificate.t0 then .review stage
        else .write stage (decide (0 ≤ menuWordScore (historyObservations state.history stage)))) next
    cases hw : state.ledger.written stage with
    | none =>
      simp only
      split
      · exact ⟨_, .review state stage ⟨ha, rfl⟩ hw (.inl rfl)⟩
      · exact ⟨_, .write state stage _ ⟨ha, rfl⟩ hw (.inl rfl)⟩
    | some bit =>
      simp only
      exact ⟨_, .advance state stage ⟨ha, rfl⟩ (by rw [hw]; exact Option.some_ne_none bit) (.inl rfl)⟩
  · simpa only [majorityAtState, hstage, dite_false] using
      (show ∃ next, Step (P.input fee hfee) C.val .uncapped accounting tapes state .stop next from
        ⟨stopState state false, .stop state ha⟩)

theorem majorityRule_eq_atState (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state)
    (ha : state.halted = false) : P.majorityRule seed state.history = majorityAtState P state := by
  have heq := majorityCandidate_eq_atState P fee hfee C accounting seed truth tapes hp ha
  obtain ⟨next, hs⟩ := majorityAtState_step P fee hfee C accounting tapes state ha
  rw [← heq] at hs
  have hallow := historyAllowsAction_of_current_step (P.input fee hfee) C.val C.property accounting
    P.majorityRule seed truth tapes hp hs
  simp only [majorityRule, searchGuardRule, hallow, ite_true]
  exact heq

end PDMenu
