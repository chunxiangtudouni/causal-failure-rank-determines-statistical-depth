module

public import PaperProofs.Statistics.LocalTest
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
Actual decision pushforwards and the finite-objective reduction needed before
stopped information (`price-proofs.tex:35-54`). Every pushforward calculation
uses the rule's measurability explicitly; the default probability-measure
instance for `Measure.map` is not used as evidence of pushforward semantics.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinaryExperiment

variable {Seed : Type*} [MeasurableSpace Seed]

theorem decisionLaw_apply (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (s : Set Bool) (hs : MeasurableSet s) :
    E.decisionLaw ν test x s =
      E.conditionalLaw ν x ((fun ω => test.rule.decision ω.1 ω.2) ⁻¹' s) := by
  exact Measure.map_apply test.measurable_decision hs

theorem decisionLaw_error (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) :
    E.decisionLaw ν test x {(!x)} = E.conditionalError ν test x := by
  rw [E.decisionLaw_apply ν test x {(!x)} (measurableSet_singleton (!x))]
  unfold conditionalError
  congr 1
  ext ω
  cases x <;> cases test.rule.decision ω.1 ω.2 <;> simp

theorem decisionLaw_correct (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    E.decisionLaw ν test x {x} = 1 - E.conditionalError ν test x := by
  have hcompl : ({(!x)} : Set Bool)ᶜ = {x} := by
    ext b
    cases x <;> cases b <;> simp
  rw [← hcompl, measure_compl (measurableSet_singleton (!x)) (measure_ne_top _ _),
    measure_univ, E.decisionLaw_error]

theorem decisionLaw_false_true (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) :
    E.decisionLaw ν test false {true} = E.conditionalError ν test false :=
  E.decisionLaw_error ν test false

theorem decisionLaw_true_false (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) :
    E.decisionLaw ν test true {false} = E.conditionalError ν test true :=
  E.decisionLaw_error ν test true

theorem decisionLaw_false_false (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) :
    E.decisionLaw ν test false {false} = 1 - E.conditionalError ν test false :=
  E.decisionLaw_correct ν test false

theorem decisionLaw_true_true (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) :
    E.decisionLaw ν test true {true} = 1 - E.conditionalError ν test true :=
  E.decisionLaw_correct ν test true

theorem conditionalError_le_one (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    E.conditionalError ν test x ≤ 1 := prob_le_one

/-- The positive prior masses and observation fee prohibit hiding an infinite
conditional expectation inside a finite Bayes objective. -/
theorem bayesObjective_finite_expectedSamples (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : E.bayesObjective ν test penalty ≠ ⊤) (x : Bool) :
    E.expectedSamples ν test x ≠ ⊤ := by
  have hprior : E.priorMass x ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (E.priorReal_pos x))
  have hfee : ENNReal.ofReal (E.observationFee : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr E.observationFee_real_pos)
  have hle : E.priorMass x * E.expectedObservationCharge ν test x ≤
      E.bayesObjective ν test penalty := by
    calc
      _ ≤ E.bayesObservationCharge ν test :=
        Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ x)
      _ ≤ E.bayesObjective ν test penalty := le_self_add
  intro htop
  have hweighted : E.priorMass x * E.expectedObservationCharge ν test x = ⊤ := by
    rw [E.expectedObservationCharge_eq, htop]
    simp [hfee, hprior]
  exact hfinite (top_le_iff.mp (hweighted ▸ hle))

theorem bayesObjective_finite_expectedObservationCharge (E : BinaryExperiment)
    (ν : Measure Seed) (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : E.bayesObjective ν test penalty ≠ ⊤) (x : Bool) :
    E.expectedObservationCharge ν test x ≠ ⊤ := by
  rw [E.expectedObservationCharge_eq]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (E.bayesObjective_finite_expectedSamples ν test penalty hfinite x)

theorem expectedSamples_finite_stop (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    ∀ᵐ ω ∂(E.conditionalLaw ν x), test.rule.stop ω.1 ω.2 ≠ ⊤ := by
  have h := ae_lt_top
    ((measurable_of_countable sampleCountENNReal).comp test.measurable_stop) hfinite
  filter_upwards [h] with ω hω
  intro hstop
  simp [hstop] at hω

theorem bayesObjective_finite_stop (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : E.bayesObjective ν test penalty ≠ ⊤) (x : Bool) :
    ∀ᵐ ω ∂(E.conditionalLaw ν x), test.rule.stop ω.1 ω.2 ≠ ⊤ :=
  E.expectedSamples_finite_stop ν test x
    (E.bayesObjective_finite_expectedSamples ν test penalty hfinite x)

/-- A real-valued stopping count is integrable only after proving the extended
expectation finite. The default value of `toNat` at infinity is never used to
discard a positive-mass nontermination event. -/
theorem expectedSamples_finite_integrable_toNat (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    Integrable (fun ω : Seed × E.Tape => ((test.rule.stop ω.1 ω.2).toNat : ℝ))
      (E.conditionalLaw ν x) := by
  have hm : Measurable (fun ω : Seed × E.Tape =>
      ((test.rule.stop ω.1 ω.2).toNat : ℝ)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n.toNat : ℝ))).comp test.measurable_stop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono ?_) (lt_top_iff_ne_top.mpr hfinite)
  intro ω
  change ‖((test.rule.stop ω.1 ω.2).toNat : ℝ)‖ₑ ≤
    sampleCountENNReal (test.rule.stop ω.1 ω.2)
  rw [Real.enorm_eq_ofReal (Nat.cast_nonneg _)]
  by_cases hstop : test.rule.stop ω.1 ω.2 = ⊤
  · simp [sampleCountENNReal, hstop]
  · simp [sampleCountENNReal, hstop]

theorem expectedSamples_finite_integral_toNat (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    ∫ ω, ((test.rule.stop ω.1 ω.2).toNat : ℝ) ∂(E.conditionalLaw ν x) =
      (E.expectedSamples ν test x).toReal := by
  have hreal := E.expectedSamples_finite_integrable_toNat ν test x hfinite
  have hnonneg : ∀ ω : Seed × E.Tape, 0 ≤ ((test.rule.stop ω.1 ω.2).toNat : ℝ) :=
    fun _ => Nat.cast_nonneg _
  have hENN : ENNReal.ofReal
      (∫ ω, ((test.rule.stop ω.1 ω.2).toNat : ℝ) ∂(E.conditionalLaw ν x)) =
      E.expectedSamples ν test x := by
    rw [ofReal_integral_eq_lintegral_ofReal hreal (ae_of_all _ hnonneg)]
    apply lintegral_congr_ae
    filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with ω hω
    simp [sampleCountENNReal, hω]
  have h := congrArg ENNReal.toReal hENN
  simpa [ENNReal.toReal_ofReal (integral_nonneg hnonneg)] using h

end PaperProofs.Statistics.BinaryExperiment
