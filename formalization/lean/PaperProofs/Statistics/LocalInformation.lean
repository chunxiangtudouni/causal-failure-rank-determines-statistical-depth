module

public import PaperProofs.Statistics.BinaryKL
public import PaperProofs.Statistics.StoppedDecision

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinaryExperiment

variable {Seed : Type} [MeasurableSpace Seed]

/-- Information demanded by the test's actual decision, not a MAP replacement. -/
noncomputable def decisionInformationDemand (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : ℝ≥0∞ :=
  (1 - E.conditionalError ν test x) * negativeLogMass (E.conditionalError ν test (!x))

/-- The original prior and observation price divided by the actual directional KL. -/
noncomputable def informationWeight (E : BinaryExperiment) (x : Bool) : ℝ≥0∞ :=
  E.priorMass x * (ENNReal.ofReal (E.observationFee : ℝ) / ENNReal.ofReal (E.divergence x))

theorem informationWeight_eq_ofReal (E : BinaryExperiment) (x : Bool) :
    E.informationWeight x =
      ENNReal.ofReal (E.priorReal x * ((E.observationFee : ℝ) / E.divergence x)) := by
  rw [informationWeight, priorMass, ← ENNReal.ofReal_div_of_pos (E.divergence_pos x),
    ← ENNReal.ofReal_mul (E.priorReal_pos x).le]

theorem informationWeight_sum (E : BinaryExperiment) :
    ∑ x : Bool, E.informationWeight x = ENNReal.ofReal E.coefficient := by
  simp_rw [E.informationWeight_eq_ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    mul_nonneg (E.priorReal_pos x).le
      (div_nonneg E.observationFee_real_pos.le (E.divergence_pos x).le))]
  congr 1
  rw [coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem informationWeight_mul_divergence (E : BinaryExperiment) (x : Bool) :
    E.informationWeight x * ENNReal.ofReal (E.divergence x) =
      E.priorMass x * ENNReal.ofReal (E.observationFee : ℝ) := by
  rw [informationWeight, mul_assoc, ENNReal.div_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (E.divergence_pos x))) ENNReal.ofReal_ne_top]

/-- The stopped-information identity is the only outstanding statistical premise.
Both finite conditional expected counts are proved separately before using it. -/
theorem decision_information_lower_of_finite (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    E.decisionInformationDemand ν test x ≤
      ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x +
        ENNReal.ofReal (Real.log 2) := by
  have hkl := E.stoppedDecisionInformationBound_of_identity hidentity
    Seed ‹MeasurableSpace Seed› ν ‹IsProbabilityMeasure ν› test hfinite x
  exact (E.decisionLaw_kl_lower ν test x).trans (add_le_add hkl le_rfl)

/-- Finite Bayes objective automatically supplies both finite conditional ETs;
there is no extra finite-stopping or MAP assumption on the test. -/
theorem decision_information_lower_of_finite_objective (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : E.bayesObjective ν test penalty ≠ ⊤) (x : Bool) :
    E.decisionInformationDemand ν test x ≤
      ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x +
        ENNReal.ofReal (Real.log 2) :=
  E.decision_information_lower_of_finite hidentity ν test
    (E.bayesObjective_finite_expectedSamples ν test penalty hfinite) x

/-- A nonnegative lower bound on actual Bayes observation charges. ENNReal
subtraction takes the positive part of each binary-information lower bound. -/
noncomputable def bayesInformationLower (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) : ℝ≥0∞ :=
  ∑ x : Bool, E.informationWeight x *
    (E.decisionInformationDemand ν test x - ENNReal.ofReal (Real.log 2))

/-- This bound includes infinite-cost rules. They satisfy the inequality in
ENNReal directly; only the finite-cost branch invokes stopped information. -/
theorem bayesInformationLower_le_observationCharge (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) :
    E.bayesInformationLower ν test ≤ E.bayesObservationCharge ν test := by
  by_cases hfinite : E.bayesObservationCharge ν test = ⊤
  · rw [hfinite]
    exact le_top
  · have hobjective : E.bayesObjective ν test 0 ≠ ⊤ := by
      simpa only [bayesObjective, zero_mul, add_zero] using hfinite
    have hcounts := E.bayesObjective_finite_expectedSamples ν test 0 hobjective
    unfold bayesInformationLower bayesObservationCharge
    apply Finset.sum_le_sum
    intro x _
    have hinfo := E.decision_information_lower_of_finite hidentity ν test hcounts x
    have hsub : E.decisionInformationDemand ν test x - ENNReal.ofReal (Real.log 2) ≤
        ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x :=
      (tsub_le_iff_right).mpr hinfo
    calc
      _ ≤ E.informationWeight x *
          (ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x) :=
        mul_le_mul' le_rfl hsub
      _ = E.priorMass x * E.expectedObservationCharge ν test x := by
        rw [← mul_assoc, E.informationWeight_mul_divergence,
          mul_assoc, E.expectedObservationCharge_eq]

theorem bayesInformationLower_le_objective (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞) :
    E.bayesInformationLower ν test ≤ E.bayesObjective ν test penalty :=
  (E.bayesInformationLower_le_observationCharge hidentity ν test).trans le_self_add

theorem bayesObjective_lower_of_identity (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞) :
    E.bayesInformationLower ν test + penalty * E.bayesError ν test ≤
      E.bayesObjective ν test penalty :=
  add_le_add (E.bayesInformationLower_le_observationCharge hidentity ν test) le_rfl

end PaperProofs.Statistics.BinaryExperiment
