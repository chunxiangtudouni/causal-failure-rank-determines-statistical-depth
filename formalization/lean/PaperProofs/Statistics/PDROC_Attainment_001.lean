module

public import PaperProofs.Statistics.BSCRoc

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Statistics.PDROC

open BinarySymmetric BinarySymmetric.Parameters

theorem rocEndpointTest_map (P : Parameters) (m : ℕ) (seed : Bool)
    (tape : P.experiment.Tape) (n : ℕ)
    (hs : (P.rocEndpointTest m).rule.stop seed tape = (n : ℕ∞)) :
    if (P.rocEndpointTest m).rule.decision seed tape then
      0 ≤ P.experiment.logOddsScore tape n else P.experiment.logOddsScore tape n ≤ 0 := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 0 := by
      have h : (0 : ℕ∞) = (n : ℕ∞) := hs
      exact (ENat.natCast_inj.mp h).symm
    subst n
    rw [P.logOddsScore_eq_signed, P.signedSum_zero]
    simp
  · rw [rocEndpointTest, ite_eq_right hm] at hs
    change (P.symmetricHittingTest m).rule.stop () tape = (n : ℕ∞) at hs
    have hd := (P.experiment.posteriorSPRT_isPosteriorThresholdRule (P.endpointError m)).2 tape n hs
    change (P.symmetricHittingTest m).rule.decision () tape = _ at hd
    have he : (P.rocEndpointTest m).rule.decision seed tape =
        decide (0 ≤ P.experiment.logOddsScore tape n) := by
      simpa only [rocEndpointTest, hm, ↓reduceIte, hittingTestOnBool] using hd
    rw [he]
    by_cases h : 0 ≤ P.experiment.logOddsScore tape n
    · simp only [h, decide_true, ↓reduceIte]
    · simpa only [h, decide_false, Bool.false_eq_true, ↓reduceIte] using (lt_of_not_ge h).le

theorem adjacentMixtureTest_map (P : Parameters) (m : ℕ) (seed : Bool × Bool)
    (tape : P.experiment.Tape) (n : ℕ)
    (hs : (P.adjacentMixtureTest m).rule.stop seed tape = (n : ℕ∞)) :
    if (P.adjacentMixtureTest m).rule.decision seed tape then
      0 ≤ P.experiment.logOddsScore tape n else P.experiment.logOddsScore tape n ≤ 0 := by
  cases hb : seed.1 <;> simp only [adjacentMixtureTest, hb, Bool.false_eq_true, ↓reduceIte] at hs ⊢
  · exact rocEndpointTest_map P (m + 1) seed.2 tape n hs
  · exact rocEndpointTest_map P m seed.2 tape n hs

universe u

def complementTest (E : BinaryExperiment) {Seed : Type u} [MeasurableSpace Seed]
    (test : E.AdmissibleRule Seed) : E.AdmissibleRule Seed where
  rule := {
    stop := test.rule.stop
    decision := fun seed tape => !(test.rule.decision seed tape)
    stopping := test.rule.stopping
    stoppedDecision := by
      intro seed tape tape' n hs hs' hp
      dsimp only
      rw [test.rule.stoppedDecision seed tape tape' n hs hs' hp]
  }
  measurable_stop := test.measurable_stop
  measurable_decision := (measurable_of_countable Bool.not).comp test.measurable_decision

theorem complementTest_conditionalError (E : BinaryExperiment) {Seed : Type u}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : E.AdmissibleRule Seed) (x : Bool) :
    E.conditionalError ν (complementTest E test) x = 1 - E.conditionalError ν test x := by
  have heq : {ω : Seed × E.Tape | (complementTest E test).rule.decision ω.1 ω.2 ≠ x} =
      {ω : Seed × E.Tape | test.rule.decision ω.1 ω.2 ≠ x}ᶜ := by
    ext ω
    cases x <;> cases h : test.rule.decision ω.1 ω.2 <;> simp [complementTest, h]
  unfold BinaryExperiment.conditionalError
  have hm : MeasurableSet {ω : Seed × E.Tape | test.rule.decision ω.1 ω.2 ≠ x} :=
    (test.measurable_decision (measurableSet_singleton x)).compl
  rw [heq, measure_compl hm]
  · simp
  · simp

theorem complementTest_expectedCharge (E : BinaryExperiment) {Seed : Type u}
    [MeasurableSpace Seed] (ν : Measure Seed) (test : E.AdmissibleRule Seed) (x : Bool) :
    E.expectedObservationCharge ν (complementTest E test) x = E.expectedObservationCharge ν test x := rfl

theorem bayesError_of_conditional (E : BinaryExperiment) {Seed : Type u}
    [MeasurableSpace Seed] (ν : Measure Seed) (test : E.AdmissibleRule Seed) (p : ℝ≥0∞)
    (h : ∀ x, E.conditionalError ν test x = p) : E.bayesError ν test = p := by
  simp only [BinaryExperiment.bayesError, h, ← Finset.sum_mul, E.priorMass_sum, one_mul]

theorem bayesCharge_of_conditional (E : BinaryExperiment) {Seed : Type u}
    [MeasurableSpace Seed] (ν : Measure Seed) (test : E.AdmissibleRule Seed) (c : ℝ≥0∞)
    (h : ∀ x, E.expectedObservationCharge ν test x = c) : E.bayesObservationCharge ν test = c := by
  simp only [BinaryExperiment.bayesObservationCharge, h, ← Finset.sum_mul, E.priorMass_sum, one_mul]

theorem rocMAPAttains_of_adjacent (P : Parameters) (h : P.RocAdjacentMixtureAttains) :
    P.RocMAPAttains := by
  intro p hp hh
  obtain ⟨he, hc⟩ := h p hp hh
  exact ⟨he, hc, adjacentMixtureTest_map P (P.rocIndex p hp)⟩

theorem rocArbitraryDecisionAttains_of_adjacent (P : Parameters) (h : P.RocAdjacentMixtureAttains) :
    P.RocArbitraryDecisionAttains := by
  intro e he heone
  let p := min e (1 - e)
  have hp : 0 < p := lt_min he (by linarith)
  have hh : p ≤ 1 / 2 := by
    by_cases hel : e ≤ 1 / 2
    · exact (min_le_left _ _).trans hel
    · exact (min_le_right _ _).trans (by linarith)
  let ν := adjacentMixtureSeedLaw (P.rocInitialWeight p hp hh)
  let base := P.adjacentMixtureTest (P.rocIndex p hp)
  obtain ⟨herr, hcost⟩ := h p hp hh
  refine ⟨hp, hh, ν, inferInstance, rfl, ?_⟩
  by_cases hel : e ≤ 1 / 2
  · have hpe : p = e := min_eq_left (by linarith)
    refine ⟨base, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro seed tape
      simp only [hel, ↓reduceIte]
      rfl
    · rw [bayesError_of_conditional P.experiment ν base _ herr, hpe]
    · exact bayesCharge_of_conditional P.experiment ν base _ hcost
  · have hpe : p = 1 - e := min_eq_right (by linarith)
    refine ⟨complementTest P.experiment base, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro seed tape
      simp only [hel, ↓reduceIte, complementTest]
      rfl
    · apply bayesError_of_conditional
      intro x
      rw [complementTest_conditionalError, herr x, hpe]
      have hsub : ENNReal.ofReal (1 - (1 - e)) =
          ENNReal.ofReal 1 - ENNReal.ofReal (1 - e) :=
        ENNReal.ofReal_sub 1 (by linarith)
      simpa only [sub_sub_cancel, ENNReal.ofReal_one] using hsub.symm
    · apply bayesCharge_of_conditional
      intro x
      exact (complementTest_expectedCharge P.experiment ν base x).trans (hcost x)

end PaperProofs.Statistics.PDROC
