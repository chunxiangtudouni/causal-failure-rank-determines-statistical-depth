module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_002
public import PaperProofs.Paid.PDMenu_MenuFramedEndpoint_094

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedRuntime

theorem cappedStop_le_iff (P : Parameters) (level : ℕ) (tape : P.experiment.Tape) (reviews : ℕ) :
    P.cappedStop level tape ≤ reviews ↔
      (∃ j ≤ reviews, level + 1 ≤ (menuWordScore (List.ofFn (fun i : Fin j => (tape i.val).val))).natAbs) ∨
        P.certificate.Q ≤ reviews := by
  change min ((P.binarySymmetric.symmetricHittingTest (level + 1)).rule.stop () tape)
    (P.certificate.Q : ℕ∞) ≤ (reviews : ℕ∞) ↔ _
  rw [min_le_iff]
  exact or_congr (PDMenu.menuScore_hitting_stop_le P.binarySymmetric (level + 1) tape reviews)
    ENat.natCast_le_natCast

theorem cappedStop_before (P : Parameters) (level : ℕ) (tape : P.experiment.Tape) (reviews : ℕ)
    (hbefore : (reviews : ℕ∞) < P.cappedStop level tape) :
    ¬(level + 1 ≤ (menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs ∨
      P.certificate.Q ≤ reviews) := by
  intro h
  apply not_le_of_gt hbefore
  apply (cappedStop_le_iff P level tape reviews).mpr
  exact h.elim (fun hh => .inl ⟨reviews, le_rfl, hh⟩) Or.inr

theorem cappedStop_at (P : Parameters) (level : ℕ) (tape : P.experiment.Tape) (reviews : ℕ)
    (hat : P.cappedStop level tape = reviews) :
    level + 1 ≤ (menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs ∨
      P.certificate.Q ≤ reviews := by
  rcases (cappedStop_le_iff P level tape reviews).mp hat.le with ⟨j, hj, hh⟩ | hQ
  · have hstopj : P.cappedStop level tape ≤ j :=
      (cappedStop_le_iff P level tape j).mpr (.inl ⟨j, le_rfl, hh⟩)
    rw [hat] at hstopj
    have heq : j = reviews := le_antisymm hj (ENat.natCast_le_natCast.mp hstopj)
    exact .inl (heq ▸ hh)
  · exact .inr hQ

theorem cappedDecision_at (P : Parameters) (level : ℕ) (tie : Bool)
    (tape : P.experiment.Tape) (reviews : ℕ) (hat : P.cappedStop level tape = reviews) :
    P.cappedDecision level tie tape =
      if menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val)) = 0 then tie else
        decide (0 ≤ menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))) := by
  let score := menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))
  have hzero : P.binarySymmetric.h * (score : ℝ) = 0 ↔ score = 0 := by
    simp only [mul_eq_zero, P.binarySymmetric.h_pos.ne', false_or, Int.cast_eq_zero]
  have hsign : 0 ≤ P.binarySymmetric.h * (score : ℝ) ↔ 0 ≤ score := by
    rw [mul_nonneg_iff_of_pos_left P.binarySymmetric.h_pos]
    constructor <;> intro h <;> exact_mod_cast h
  have hscore : P.binarySymmetric.experiment.logOddsScore tape reviews = P.binarySymmetric.h * (score : ℝ) :=
    PDMenu.menuScore_logOdds P.binarySymmetric tape reviews
  simp only [cappedDecision, hat, ENat.toNat_natCast]
  rw [hscore]
  simp only [hzero, hsign]
  with_unfolding_all rfl

theorem calibratedTest_positive_stop (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool × Bool) (tape : P.experiment.Tape) :
    (P.calibratedTest level).rule.stop seed tape =
      if seed.1 then P.cappedStop level tape else 0 := by
  simp only [calibratedTest, hlevel, ite_false, cappedTest,
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessTest]

theorem calibratedTest_positive_decision (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool × Bool) (tape : P.experiment.Tape) :
    (P.calibratedTest level).rule.decision seed tape =
      if seed.1 then P.cappedDecision level seed.2 tape else seed.2 := by
  simp only [calibratedTest, hlevel, ite_false, cappedTest,
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessTest]

theorem cappedTestingAction_reviewFrame (P : Parameters) (level : ℕ) (tie : Bool)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (tape : ((P.input fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent P.sharedInstance)) (reviews : ℕ)
    (ho : historyObservations before stage = []) :
    P.cappedTestingAction level tie
      (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage =
        if level + 1 ≤ (menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs ∨
          P.certificate.Q ≤ reviews then
          .write stage (if menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val)) = 0 then tie
            else decide (0 ≤ menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))))
        else .review stage := by
  have hletters : (List.ofFn (fun i : Fin reviews => (tape i.val).val)).all (fun symbol => symbol < 2) = true := by
    apply List.all_eq_true.mpr
    intro symbol hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact decide_eq_true (tape i.val).isLt
  have hword : historyObservations
      (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage =
        List.ofFn (fun i : Fin reviews => (tape i.val).val) := by
    rw [PDMenu.menuReviewFrame_observations, ho, List.nil_append]
  simp only [cappedTestingAction, hword, hletters, ite_true, List.length_ofFn]

/-- Before the actual calibrated stop, the actual visible command is a
review of precisely this physical stage. -/
theorem calibratedTestingAction_beforeStop (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (seed : P.CalibratedMenuSeed)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (tape : ((P.input fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent P.sharedInstance)) (reviews : ℕ)
    (ho : historyObservations before stage = [])
    (hbefore : (reviews : ℕ∞) < (calibratedStageTest P level).rule.stop
      (seed.1 stage, seed.2 stage) tape) :
    P.calibratedTestingAction level seed
      (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage = .review stage := by
  let row : StageSeed P := (seed.1 stage, seed.2 stage)
  let originalTape : P.experiment.Tape := tape
  replace hbefore : (reviews : ℕ∞) < (calibratedStageTest P level).rule.stop row originalTape := hbefore
  with_unfolding_all rw [calibratedStageTest_stop, localCalibrationSeed_of_valid P level _ valid] at hbefore
  by_cases hz : level = 0
  · subst level
    have hzstop : (P.calibratedTest 0).rule.stop (row.2 ⟨0, by omega⟩, row.1) originalTape = 0 :=
      PDMenu.calibratedTest_zero_stop P ((row.2 ⟨0, by omega⟩, row.1), originalTape)
    exact (not_lt_zero (lt_of_lt_of_eq hbefore hzstop)).elim
  · with_unfolding_all rw [calibratedTest_positive_stop P level hz] at hbefore
    cases hmark : row.2 ⟨level, by omega⟩
    · simp only [hmark, Bool.false_eq_true, ite_false] at hbefore
      exact (not_lt_zero hbefore).elim
    · simp only [hmark, ite_true] at hbefore
      have hnot := cappedStop_before P level originalTape reviews hbefore
      have hmarkActual : seed.2 stage ⟨level, by omega⟩ = true := hmark
      with_unfolding_all simp only [calibratedTestingAction, hz, ite_false, dite_eq_left valid, hmarkActual, ite_true]
      with_unfolding_all rw [cappedTestingAction_reviewFrame P level (seed.1 stage) fee hfee stage tape before reviews ho]
      exact ite_eq_right hnot

/-- At its actual finite calibrated stop, the controller writes exactly
the original calibratedTest decision, including the blind and fair-tie cases. -/
theorem calibratedTestingAction_atStop (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (seed : P.CalibratedMenuSeed)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (tape : ((P.input fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent P.sharedInstance)) (reviews : ℕ)
    (ho : historyObservations before stage = [])
    (hat : (calibratedStageTest P level).rule.stop (seed.1 stage, seed.2 stage) tape = reviews) :
    P.calibratedTestingAction level seed
      (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage =
        .write stage ((calibratedStageTest P level).rule.decision (seed.1 stage, seed.2 stage) tape) := by
  let row : StageSeed P := (seed.1 stage, seed.2 stage)
  let originalTape : P.experiment.Tape := tape
  replace hat : (calibratedStageTest P level).rule.stop row originalTape = reviews := hat
  change P.calibratedTestingAction level seed
    (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage =
      .write stage ((calibratedStageTest P level).rule.decision row originalTape)
  with_unfolding_all rw [calibratedStageTest_stop, localCalibrationSeed_of_valid P level _ valid] at hat
  with_unfolding_all rw [calibratedStageTest_decision, localCalibrationSeed_of_valid P level _ valid]
  by_cases hz : level = 0
  · subst level
    have hd : (P.calibratedTest 0).rule.decision (row.2 ⟨0, by omega⟩, row.1) originalTape = row.1 :=
      PDMenu.calibratedTest_zero_decision P ((row.2 ⟨0, by omega⟩, row.1), originalTape)
    exact (calibratedTestingAction_zero P seed _ stage).trans (congrArg (Action.write stage) hd.symm)
  · with_unfolding_all rw [calibratedTest_positive_stop P level hz] at hat
    with_unfolding_all rw [calibratedTest_positive_decision P level hz]
    cases hmark : row.2 ⟨level, by omega⟩
    · have hmarkActual : seed.2 stage ⟨level, by omega⟩ = false := hmark
      with_unfolding_all simp only [calibratedTestingAction, hz, ite_false, dite_eq_left valid,
        hmarkActual, Bool.false_eq_true]
      with_unfolding_all rfl
    · simp only [hmark, ite_true] at hat ⊢
      have hhit := cappedStop_at P level originalTape reviews hat
      have hmarkActual : seed.2 stage ⟨level, by omega⟩ = true := hmark
      with_unfolding_all simp only [calibratedTestingAction, hz, ite_false, dite_eq_left valid, hmarkActual, ite_true]
      with_unfolding_all rw [cappedTestingAction_reviewFrame P level (seed.1 stage) fee hfee stage tape before reviews ho,
        ite_eq_left hhit]
      exact congrArg (Action.write stage) (cappedDecision_at P level row.1 originalTape reviews hat).symm

end PDROC.CalibratedRuntime
