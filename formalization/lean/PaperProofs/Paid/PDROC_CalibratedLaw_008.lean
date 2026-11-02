module

public import PaperProofs.Paid.PDROC_CalibratedLaw_003
public import PaperProofs.Paid.PDROC_CalibratedLaw_004
public import PaperProofs.Paid.PDROC_CalibratedLaw_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

theorem pathOutcome_integral_eq (P : Parameters) (table : MenuTable) (valid : TableLevelsValid P table) :
    ∀ n k (f : Outcome → ℝ≥0∞),
    (∫⁻ sample : TailOf P (StageSeed P) n,
      f (pathSummary P (calibratedFamily P) table n k sample.1 sample.2).outcome ∂inputLaw P (stageSeedLaw P) n) =
    (∫⁻ sample : TailOf P Bool n,
      f (pathSummary P (idealFamily P) table n k sample.1 sample.2).outcome
      ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) := by
  classical
  intro n
  induction n with
  | zero => intro k f; simp [pathSummary, finishRecord, PathRecord.outcome]
  | succ n ih =>
    intro k f
    cases action : (menuEntryAt table (n + 1) k).action with
    | finish => simp [pathSummary, action]
    | abandon => simp [pathSummary, action]
    | test level bad =>
      have levelValid := valid (n + 1) k level bad action
      have finiteCal : ∀ᵐ head ∂(stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P),
          (calibratedStageTest P level).rule.stop head.1 head.2.2 ≠ ⊤ :=
        Filter.Eventually.of_forall (head_stop_finite P level)
      have finiteIdeal := PDROC.MenuExpected.head_stop_ae_finite P level
      have goodCal : ((stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (calibratedStageTest P level)) =
          ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) := correct_mass P level levelValid
      have badCal : ((stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (calibratedStageTest P level))ᶜ =
          ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := wrong_mass P level levelValid
      have goodIdeal : (BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (PDMenu.menuAnalysisTest P level)) =
          ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) := PDROC.MenuExpected.correct_mass P level
      have badIdeal : (BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (PDMenu.menuAnalysisTest P level))ᶜ =
          ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := PDROC.MenuExpected.wrong_mass P level
      rw [outcome_integral_step P (stageSeedLaw P) (calibratedFamily P) table n k level bad
          (calibratedStageTest P level) action (calibratedFamily_some P level levelValid) finiteCal f,
        outcome_integral_step P BinarySymmetric.Parameters.fairGuessLaw (idealFamily P) table n k level bad
          (PDMenu.menuAnalysisTest P level) action rfl finiteIdeal f,
        goodCal, badCal, goodIdeal, badIdeal]
      have good := ih k (fun outcome => f (prependOutcome (false, false) outcome))
      have wrong :
          (∫⁻ tail : TailOf P (StageSeed P) n, f (badOutcomeTail P (calibratedFamily P) table n k bad tail)
            ∂inputLaw P (stageSeedLaw P) n) =
          (∫⁻ tail : TailOf P Bool n, f (badOutcomeTail P (idealFamily P) table n k bad tail)
            ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) := by
        cases bad with
        | abandon => simp [badOutcomeTail]
        | repair =>
          by_cases hk : k = 0
          · simp [badOutcomeTail, hk]
          · simpa only [badOutcomeTail, ite_eq_right hk] using
              ih (k - 1) (fun outcome => f (prependOutcome (true, true) outcome))
      rw [good, wrong]

/-- Equality of the complete visited-write/physical-repair/failure trace
law, with the genuine original nonreturn branch preserved as a null event. -/
theorem pathOutcome_law (P : Parameters) (table : MenuTable) (valid : TableLevelsValid P table) (n k : ℕ) :
    (inputLaw P (stageSeedLaw P) n).map
      (fun sample => (pathSummary P (calibratedFamily P) table n k sample.1 sample.2).outcome) =
    (inputLaw P BinarySymmetric.Parameters.fairGuessLaw n).map
      (fun sample => (pathSummary P (idealFamily P) table n k sample.1 sample.2).outcome) := by
  apply Measure.ext
  intro s hs
  let f : Outcome → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hc := lintegral_map (μ := inputLaw P (stageSeedLaw P) n) hf
    (measurable_pathOutcome P (calibratedFamily P) table n k)
  have hi := lintegral_map (μ := inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) hf
    (measurable_pathOutcome P (idealFamily P) table n k)
  dsimp only [f] at hc hi
  rw [lintegral_indicator_fun_one hs] at hc hi
  exact hc.trans ((pathOutcome_integral_eq P table valid n k f).trans hi.symm)

theorem pathObservation_integral_le_four (P : Parameters) (table : MenuTable) (valid : TableLevelsValid P table) :
    ∀ n k,
    (∫⁻ sample : TailOf P (StageSeed P) n,
      (pathSummary P (calibratedFamily P) table n k sample.1 sample.2).observation ∂inputLaw P (stageSeedLaw P) n) ≤
    4 * (∫⁻ sample : TailOf P Bool n,
      (pathSummary P (idealFamily P) table n k sample.1 sample.2).observation
      ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) := by
  classical
  intro n
  induction n with
  | zero => intro k; simp [pathSummary, finishRecord]
  | succ n ih =>
    intro k
    cases action : (menuEntryAt table (n + 1) k).action with
    | finish => simp [pathSummary, action, abandonRecord]
    | abandon => simp [pathSummary, action, abandonRecord]
    | test level bad =>
      have levelValid := valid (n + 1) k level bad action
      have finiteCal : ∀ᵐ head ∂(stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P),
          (calibratedStageTest P level).rule.stop head.1 head.2.2 ≠ ⊤ :=
        Filter.Eventually.of_forall (head_stop_finite P level)
      have finiteIdeal := PDROC.MenuExpected.head_stop_ae_finite P level
      have goodCal : ((stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (calibratedStageTest P level)) =
          ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) := correct_mass P level levelValid
      have badCal : ((stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (calibratedStageTest P level))ᶜ =
          ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := wrong_mass P level levelValid
      have goodIdeal : (BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (PDMenu.menuAnalysisTest P level)) =
          ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) := PDROC.MenuExpected.correct_mass P level
      have badIdeal : (BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P))
          (localCorrectSet P (PDMenu.menuAnalysisTest P level))ᶜ =
          ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := PDROC.MenuExpected.wrong_mass P level
      have charge :
          (∫⁻ head, localObservation P (calibratedStageTest P level) head
            ∂(stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P)) ≤
          4 * (∫⁻ head, localObservation P (PDMenu.menuAnalysisTest P level) head
            ∂BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P)) := by
        have idealCharge : (∫⁻ head, localObservation P (PDMenu.menuAnalysisTest P level) head
            ∂BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P)) =
            ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) := PDROC.MenuExpected.headCharge_integral P level
        exact (headCharge_integral_le_four P level levelValid).trans_eq (congrArg (4 * ·) idealCharge.symm)
      rw [observation_integral_step P (stageSeedLaw P) (calibratedFamily P) table n k level bad
          (calibratedStageTest P level) action (calibratedFamily_some P level levelValid) finiteCal,
        observation_integral_step P BinarySymmetric.Parameters.fairGuessLaw (idealFamily P) table n k level bad
          (PDMenu.menuAnalysisTest P level) action rfl finiteIdeal,
        goodCal, badCal, goodIdeal, badIdeal]
      have wrong :
          (∫⁻ tail : TailOf P (StageSeed P) n, badObservationTail P (calibratedFamily P) table n k bad tail
            ∂inputLaw P (stageSeedLaw P) n) ≤
          4 * (∫⁻ tail : TailOf P Bool n, badObservationTail P (idealFamily P) table n k bad tail
            ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) := by
        cases bad with
        | abandon => simp [badObservationTail]
        | repair =>
          by_cases hk : k = 0
          · simp [badObservationTail, hk]
          · simpa only [badObservationTail, ite_eq_right hk] using ih (k - 1)
      calc
        _ ≤ 4 * (∫⁻ head, localObservation P (PDMenu.menuAnalysisTest P level) head
              ∂BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P)) +
            (ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) *
              (4 * (∫⁻ tail : TailOf P Bool n,
                (pathSummary P (idealFamily P) table n k tail.1 tail.2).observation
                ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n)) +
            ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) *
              (4 * (∫⁻ tail : TailOf P Bool n, badObservationTail P (idealFamily P) table n k bad tail
                ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n))) :=
          add_le_add charge (add_le_add (mul_le_mul' le_rfl (ih k)) (mul_le_mul' le_rfl wrong))
        _ = _ := by
          simp only [mul_add]
          ac_rfl

theorem solveMenuTable_outcome_law (P : Parameters) (fee penalty : ℚ) (N K n k : ℕ) :
    (inputLaw P (stageSeedLaw P) n).map
      (fun sample => (pathSummary P (calibratedFamily P) (P.solveMenuTable fee penalty K N) n k sample.1 sample.2).outcome) =
    (inputLaw P BinarySymmetric.Parameters.fairGuessLaw n).map
      (fun sample => (pathSummary P (idealFamily P) (P.solveMenuTable fee penalty K N) n k sample.1 sample.2).outcome) :=
  pathOutcome_law P _ (solveMenuTable_levelsValid P fee penalty N K) n k

theorem solveMenuTable_observation_le_four (P : Parameters) (fee penalty : ℚ) (N K n k : ℕ) :
    (∫⁻ sample : TailOf P (StageSeed P) n,
      (pathSummary P (calibratedFamily P) (P.solveMenuTable fee penalty K N) n k sample.1 sample.2).observation
      ∂inputLaw P (stageSeedLaw P) n) ≤
    4 * (∫⁻ sample : TailOf P Bool n,
      (pathSummary P (idealFamily P) (P.solveMenuTable fee penalty K N) n k sample.1 sample.2).observation
      ∂inputLaw P BinarySymmetric.Parameters.fairGuessLaw n) :=
  pathObservation_integral_le_four P _ (solveMenuTable_levelsValid P fee penalty N K) n k

end PDROC.CalibratedLaw
