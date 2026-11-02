module

public import PaperProofs.Paid.PDROC_CalibratedLaw_005
public import PaperProofs.Paid.PDROC_MenuExpected_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

abbrev TailOf (P : Parameters) (S : Type*) (n : ℕ) := (Fin n → S) × PDMenu.MenuAnalysisWorld P n
abbrev HeadOf (P : Parameters) (S : Type*) := S × (Bool × P.experiment.Tape)

noncomputable def inputLaw (P : Parameters) {S : Type*} [MeasurableSpace S] (ν : Measure S) (n : ℕ) :
    Measure (TailOf P S n) :=
  (Measure.pi fun _ : Fin n => ν).prod (Measure.pi fun _ : Fin n => PDMenu.menuAnalysisStageLaw P)

instance inputLaw_probability (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) : IsProbabilityMeasure (inputLaw P ν n) := by
  unfold inputLaw
  infer_instance

def inputSplit (P : Parameters) {S : Type*} (n : ℕ) (sample : TailOf P S (n + 1)) :
    HeadOf P S × TailOf P S n :=
  ((sample.1 0, sample.2 0), (Fin.tail sample.1, Fin.tail sample.2))

theorem inputSplit_measurePreserving (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (inputSplit P n) (inputLaw P ν (n + 1))
      ((ν.prod (PDMenu.menuAnalysisStageLaw P)).prod (inputLaw P ν n)) := by
  have hs := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
  have hw := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => PDMenu.menuAnalysisStageLaw P) 0
  have hshuffle := BellmanExpectation.measurePreserving_pairShuffle
    ν (Measure.pi fun _ : Fin n => ν) (PDMenu.menuAnalysisStageLaw P)
    (Measure.pi fun _ : Fin n => PDMenu.menuAnalysisStageLaw P)
  exact hshuffle.comp (hs.prod hw)

def localCorrectSet (P : Parameters) {S : Type*} [MeasurableSpace S]
    (test : P.experiment.AdmissibleRule S) : Set (HeadOf P S) :=
  {head | test.rule.decision head.1 head.2.2 = head.2.1}

theorem measurableSet_localCorrectSet (P : Parameters) {S : Type*} [MeasurableSpace S]
    (test : P.experiment.AdmissibleRule S) : MeasurableSet (localCorrectSet P test) :=
  measurableSet_eq_fun (test.measurable_decision.comp (measurable_fst.prodMk measurable_snd.snd))
    measurable_snd.fst

noncomputable def localObservation (P : Parameters) {S : Type*} [MeasurableSpace S]
    (test : P.experiment.AdmissibleRule S) (head : HeadOf P S) : ℝ≥0∞ :=
  P.experiment.observationCharge (test.rule.stop head.1 head.2.2)

theorem measurable_localObservation (P : Parameters) {S : Type*} [MeasurableSpace S]
    (test : P.experiment.AdmissibleRule S) : Measurable (localObservation P test) :=
  (measurable_of_countable P.experiment.observationCharge).comp
    (test.measurable_stop.comp (measurable_fst.prodMk measurable_snd.snd))

theorem selected_input_integral (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) (test : P.experiment.AdmissibleRule S)
    (good bad : TailOf P S n → ℝ≥0∞) (hg : Measurable good) (hb : Measurable bad) :
    (∫⁻ sample : TailOf P S (n + 1),
      if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
      then good (Fin.tail sample.1, Fin.tail sample.2) else bad (Fin.tail sample.1, Fin.tail sample.2)
      ∂inputLaw P ν (n + 1)) =
      (ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test) * (∫⁻ tail, good tail ∂inputLaw P ν n) +
      (ν.prod (PDMenu.menuAnalysisStageLaw P)) (localCorrectSet P test)ᶜ * (∫⁻ tail, bad tail ∂inputLaw P ν n) := by
  classical
  let f : HeadOf P S × TailOf P S n → ℝ≥0∞ :=
    fun pair => if pair.1 ∈ localCorrectSet P test then good pair.2 else bad pair.2
  have hf : Measurable f := PDROC.MenuExpected.measurable_selected _ (measurableSet_localCorrectSet P test) _ _ hg hb
  have he : (fun sample : TailOf P S (n + 1) =>
      if test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
      then good (Fin.tail sample.1, Fin.tail sample.2) else bad (Fin.tail sample.1, Fin.tail sample.2)) =
      fun sample => f (inputSplit P n sample) := by
    funext sample
    by_cases correct : test.rule.decision (sample.1 0) (sample.2 0).2 = (sample.2 0).1
    · have member : (sample.1 0, sample.2 0) ∈ localCorrectSet P test := correct
      simp only [f, inputSplit, ite_eq_left correct, ite_eq_left member]
    · have member : (sample.1 0, sample.2 0) ∉ localCorrectSet P test := correct
      simp only [f, inputSplit, ite_eq_right correct, ite_eq_right member]
  rw [he, (inputSplit_measurePreserving P ν n).lintegral_comp hf]
  exact PDROC.MenuExpected.selected_product_integral _ _ (localCorrectSet P test)
    (measurableSet_localCorrectSet P test) good bad hg hb

theorem full_localObservation_integral (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) (test : P.experiment.AdmissibleRule S) :
    (∫⁻ sample : TailOf P S (n + 1), localObservation P test (sample.1 0, sample.2 0)
      ∂inputLaw P ν (n + 1)) = ∫⁻ head, localObservation P test head ∂ν.prod (PDMenu.menuAnalysisStageLaw P) := by
  have hf : Measurable (fun pair : HeadOf P S × TailOf P S n => localObservation P test pair.1) :=
    (measurable_localObservation P test).comp measurable_fst
  have hs := (inputSplit_measurePreserving P ν n).lintegral_comp hf
  have hp := (measurePreserving_fst (μ := ν.prod (PDMenu.menuAnalysisStageLaw P)) (ν := inputLaw P ν n)).lintegral_comp
    (measurable_localObservation P test)
  exact hs.trans hp

theorem full_localStop_ae_finite (P : Parameters) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) (test : P.experiment.AdmissibleRule S)
    (finite : ∀ᵐ head ∂ν.prod (PDMenu.menuAnalysisStageLaw P), test.rule.stop head.1 head.2.2 ≠ ⊤) :
    ∀ᵐ sample : TailOf P S (n + 1) ∂inputLaw P ν (n + 1),
      test.rule.stop (sample.1 0) (sample.2 0).2 ≠ ⊤ := by
  have hp := (measurePreserving_fst (μ := ν.prod (PDMenu.menuAnalysisStageLaw P))
    (ν := inputLaw P ν n)).quasiMeasurePreserving.ae finite
  exact (inputSplit_measurePreserving P ν n).quasiMeasurePreserving.ae hp

def prependOutcome (event : Bool × Bool) (outcome : Outcome) : Outcome := (event :: outcome.1, outcome.2)

noncomputable def badOutcomeTail (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ)
    (bad : MenuBadAction) (sample : TailOf P S n) : Outcome :=
  match bad with
  | .abandon => ([(true, false)], true)
  | .repair => if k = 0 then ([(true, false)], true) else
      prependOutcome (true, true) (pathSummary P tests table n (k - 1) sample.1 sample.2).outcome

theorem measurable_badOutcomeTail (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ) (bad : MenuBadAction) :
    Measurable (badOutcomeTail P tests table n k bad) := by
  classical
  cases bad with
  | abandon => exact measurable_const
  | repair =>
    by_cases hk : k = 0
    · have he : badOutcomeTail P tests table n k .repair =
          (fun _ : TailOf P S n => ([(true, false)], true)) := by
        funext sample
        exact ite_eq_left hk
      rw [he]
      exact measurable_const
    · have he : badOutcomeTail P tests table n k .repair =
          (fun sample : TailOf P S n => prependOutcome (true, true)
            (pathSummary P tests table n (k - 1) sample.1 sample.2).outcome) := by
        funext sample
        exact ite_eq_right hk
      rw [he]
      exact (measurable_of_countable (prependOutcome (true, true))).comp (measurable_pathOutcome P tests table n (k - 1))

noncomputable def badObservationTail (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ)
    (bad : MenuBadAction) (sample : TailOf P S n) : ℝ≥0∞ :=
  match bad with
  | .abandon => 0
  | .repair => if k = 0 then 0 else (pathSummary P tests table n (k - 1) sample.1 sample.2).observation

theorem measurable_badObservationTail (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable) (n k : ℕ) (bad : MenuBadAction) :
    Measurable (badObservationTail P tests table n k bad) := by
  classical
  cases bad with
  | abandon => exact measurable_const
  | repair =>
    by_cases hk : k = 0
    · have he : badObservationTail P tests table n k .repair = (fun _ : TailOf P S n => 0) := by
        funext sample
        exact ite_eq_left hk
      rw [he]
      exact measurable_const
    · have he : badObservationTail P tests table n k .repair =
          (fun sample : TailOf P S n => (pathSummary P tests table n (k - 1) sample.1 sample.2).observation) := by
        funext sample
        exact ite_eq_right hk
      rw [he]
      exact measurable_pathObservation P tests table n (k - 1)

theorem pathSummary_outcome_test (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level : ℕ) (bad : MenuBadAction) (test : P.experiment.AdmissibleRule S)
    (action : (menuEntryAt table (n + 1) k).action = .test level bad) (selected : tests level = some test)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (finite : test.rule.stop (seed 0) (world 0).2 ≠ ⊤) :
    (pathSummary P tests table (n + 1) k seed world).outcome =
      if test.rule.decision (seed 0) (world 0).2 = (world 0).1 then
        prependOutcome (false, false) (pathSummary P tests table n k (Fin.tail seed) (Fin.tail world)).outcome
      else badOutcomeTail P tests table n k bad (Fin.tail seed, Fin.tail world) := by
  classical
  cases bad <;> by_cases hk : k = 0 <;> split_ifs <;>
    simp_all only [pathSummary, PathRecord.outcome, badOutcomeTail, prependOutcome,
      abandonRecord, ite_true, ite_false]

theorem pathSummary_observation_test (P : Parameters) {S : Type*} [MeasurableSpace S]
    (tests : ℕ → Option (P.experiment.AdmissibleRule S)) (table : MenuTable)
    (n k level : ℕ) (bad : MenuBadAction) (test : P.experiment.AdmissibleRule S)
    (action : (menuEntryAt table (n + 1) k).action = .test level bad) (selected : tests level = some test)
    (seed : Fin (n + 1) → S) (world : PDMenu.MenuAnalysisWorld P (n + 1))
    (finite : test.rule.stop (seed 0) (world 0).2 ≠ ⊤) :
    (pathSummary P tests table (n + 1) k seed world).observation =
      localObservation P test (seed 0, world 0) +
        if test.rule.decision (seed 0) (world 0).2 = (world 0).1 then
          (pathSummary P tests table n k (Fin.tail seed) (Fin.tail world)).observation
        else badObservationTail P tests table n k bad (Fin.tail seed, Fin.tail world) := by
  classical
  cases bad <;> by_cases hk : k = 0 <;> split_ifs <;>
    simp_all only [pathSummary, badObservationTail, localObservation,
      abandonRecord, ite_true, ite_false]

end PDROC.CalibratedLaw
