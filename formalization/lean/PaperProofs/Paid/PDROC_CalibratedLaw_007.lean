module

public import PaperProofs.Paid.PDROC_CalibratedLaw_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

/-- Exact complete-outcome recursion under a genuinely fresh whole head
row. Local nonreturn is removed only on the explicitly proved null set;
the path-summary definition itself still retains its infinite branch. -/
theorem outcome_integral_step (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level : ℕ) (bad : MenuBadAction) (test : P.experiment.AdmissibleRule S)
    (action : (menuEntryAt table (n + 1) k).action = .test level bad) (selected : tests level = some test)
    (finite : ∀ᵐ head ∂ν.prod (PDMenu.menuAnalysisStageLaw P), test.rule.stop head.1 head.2.2 ≠ ⊤)
    (f : Outcome → ℝ≥0∞) :
    (∫⁻ sample : TailOf P S (n + 1), f (pathSummary P tests table (n + 1) k sample.1 sample.2).outcome
      ∂inputLaw P ν (n + 1)) =
      (ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test) *
        (∫⁻ tail : TailOf P S n,
          f (prependOutcome (false, false) (pathSummary P tests table n k tail.1 tail.2).outcome) ∂inputLaw P ν n) +
      (ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test)ᶜ *
        (∫⁻ tail : TailOf P S n, f (badOutcomeTail P tests table n k bad tail) ∂inputLaw P ν n) := by
  classical
  have hfinite := full_localStop_ae_finite P ν n test finite
  have hf : Measurable f := measurable_of_countable _
  calc
    _ = ∫⁻ sample : TailOf P S (n + 1),
        if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1 then
          f (prependOutcome (false, false) (pathSummary P tests table n k (Fin.tail sample.1) (Fin.tail sample.2)).outcome)
        else f (badOutcomeTail P tests table n k bad (Fin.tail sample.1, Fin.tail sample.2))
        ∂inputLaw P ν (n + 1) := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with sample hs
      rw [pathSummary_outcome_test P tests table n k level bad test action selected sample.1 sample.2 hs]
      split_ifs <;> rfl
    _ = _ := selected_input_integral P ν n test _ _
      (hf.comp ((measurable_of_countable (prependOutcome (false, false))).comp (measurable_pathOutcome P tests table n k)))
      (hf.comp (measurable_badOutcomeTail P tests table n k bad))

/-- Positive observation recursion. Test duration may correlate with the
head error: only independence of the full head from the tail is used. -/
theorem observation_integral_step (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level : ℕ) (bad : MenuBadAction) (test : P.experiment.AdmissibleRule S)
    (action : (menuEntryAt table (n + 1) k).action = .test level bad) (selected : tests level = some test)
    (finite : ∀ᵐ head ∂ν.prod (PDMenu.menuAnalysisStageLaw P), test.rule.stop head.1 head.2.2 ≠ ⊤) :
    (∫⁻ sample : TailOf P S (n + 1), (pathSummary P tests table (n + 1) k sample.1 sample.2).observation
      ∂inputLaw P ν (n + 1)) =
      (∫⁻ head, localObservation P test head ∂ν.prod (PDMenu.menuAnalysisStageLaw P)) +
      ((ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test) *
        (∫⁻ tail : TailOf P S n, (pathSummary P tests table n k tail.1 tail.2).observation ∂inputLaw P ν n) +
      (ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test)ᶜ *
        (∫⁻ tail : TailOf P S n, badObservationTail P tests table n k bad tail ∂inputLaw P ν n)) := by
  classical
  have hfinite := full_localStop_ae_finite P ν n test finite
  have hcharge : Measurable (fun sample : TailOf P S (n + 1) => localObservation P test (sample.1 0, sample.2 0)) :=
    (measurable_localObservation P test).comp
      (((measurable_pi_apply 0).comp measurable_fst).prodMk ((measurable_pi_apply 0).comp measurable_snd))
  calc
    _ = ∫⁻ sample : TailOf P S (n + 1), localObservation P test (sample.1 0, sample.2 0) +
        (if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1 then
          (pathSummary P tests table n k (Fin.tail sample.1) (Fin.tail sample.2)).observation
        else badObservationTail P tests table n k bad (Fin.tail sample.1, Fin.tail sample.2))
        ∂inputLaw P ν (n + 1) := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with sample hs
      exact pathSummary_observation_test P tests table n k level bad test action selected sample.1 sample.2 hs
    _ = _ := by
      rw [lintegral_add_left hcharge, full_localObservation_integral P ν n test,
        selected_input_integral P ν n test _ _ (measurable_pathObservation P tests table n k)
          (measurable_badObservationTail P tests table n k bad)]

/-- The enriched ideal summary changes only analysis bookkeeping: its
observation field is pointwise exactly the already-frozen D18 summary. -/
theorem ideal_observation_eq_menu (P : Parameters) (table : MenuTable) :
    ∀ n k (seed : Fin n → Bool) (world : PDMenu.MenuAnalysisWorld P n),
      (pathSummary P (idealFamily P) table n k seed world).observation =
        (PDMenu.menuPathSummary P table n k seed world).observation := by
  classical
  intro n
  induction n with
  | zero => intro k seed world; rfl
  | succ n ih =>
    intro k seed world
    cases action : (menuEntryAt table (n + 1) k).action with
    | finish => simp only [pathSummary, PDMenu.menuPathSummary, action]; rfl
    | abandon => simp only [pathSummary, PDMenu.menuPathSummary, action]; rfl
    | test level bad =>
      by_cases finite : (PDMenu.menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = ⊤
      · simp only [pathSummary, idealFamily, PDMenu.menuPathSummary, action, finite, ite_true]
        rfl
      · by_cases correct : (PDMenu.menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 = (world 0).1
        · simpa only [pathSummary, idealFamily, PDMenu.menuPathSummary, action,
            ite_eq_right finite, ite_eq_left correct] using
            congrArg (fun value => P.experiment.observationCharge
              ((PDMenu.menuAnalysisTest P level).rule.stop (seed 0) (world 0).2) + value)
              (ih k (Fin.tail seed) (Fin.tail world))
        · cases bad with
          | abandon =>
            simp only [pathSummary, idealFamily, PDMenu.menuPathSummary, action,
              ite_eq_right finite, ite_eq_right correct]
            rfl
          | repair =>
            by_cases hk : k = 0
            · subst k
              simp only [pathSummary, idealFamily, PDMenu.menuPathSummary, action,
                ite_eq_right finite, ite_eq_right correct, ite_true]
              rfl
            · simpa only [pathSummary, idealFamily, PDMenu.menuPathSummary, action,
                ite_eq_right finite, ite_eq_right correct, ite_eq_right hk] using
                congrArg (fun value => P.experiment.observationCharge
                  ((PDMenu.menuAnalysisTest P level).rule.stop (seed 0) (world 0).2) + value)
                  (ih (k - 1) (Fin.tail seed) (Fin.tail world))

end PDROC.CalibratedLaw
