module

public import PaperProofs.Statistics.PDROC_Lower_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics.BinarySymmetric

namespace PDROC

theorem rocChord_affine (P : Parameters) (m : ℕ) (p : ℝ) :
    P.rocChord m p =
      (((P.endpointCharge m : ℝ) - (P.endpointCharge (m + 1) : ℝ)) /
        ((P.endpointError m : ℝ) - (P.endpointError (m + 1) : ℝ))) * p +
      ((P.endpointCharge (m + 1) : ℝ) -
        (((P.endpointCharge m : ℝ) - (P.endpointCharge (m + 1) : ℝ)) /
          ((P.endpointError m : ℝ) - (P.endpointError (m + 1) : ℝ))) *
          (P.endpointError (m + 1) : ℝ)) := by
  unfold Parameters.rocChord Parameters.rocWeight
  ring

theorem rocChord_integrable (P : Parameters) (m : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) : Integrable (fun ω => P.rocChord m (f ω)) μ := by
  simp_rw [rocChord_affine]
  exact (hf.const_mul _).add (integrable_const _)

theorem integral_rocChord (P : Parameters) (m : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) :
    (∫ ω, P.rocChord m (f ω) ∂μ) = P.rocChord m (∫ ω, f ω ∂μ) := by
  simp_rw [rocChord_affine]
  rw [integral_add (hf.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp

universe u

/-- Integrating the discrete supporting secant gives the original observation
fee lower bound at any error above the actual mean posterior error. This is a
component: the posterior-average premise is discharged separately for every
admissible decision, rather than inserted into the decision class. -/
theorem rocPrice_le_charge_of_posterior_average (P : Parameters) {Seed : Type u}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hf : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤)
    [IsProbabilityMeasure (P.bayesStoppedLaw ν test)]
    (hi : Integrable (fun record : Seed × P.experiment.StoppedWord =>
      P.wordPosteriorError record.2) (P.bayesStoppedLaw ν test))
    (p : ℝ) (hp : 0 < p) (hh : p ≤ 1 / 2)
    (he : (∫ record : Seed × P.experiment.StoppedWord,
      P.wordPosteriorError record.2 ∂(P.bayesStoppedLaw ν test)) ≤ p) :
    P.rocPrice p ≤ P.experiment.bayesObservationCharge ν test := by
  let μ := P.bayesStoppedLaw ν test
  let m := P.rocIndex p hp
  have hphi := P.posteriorPhi_integrable ν test hf
  have hbound : P.rocChord m p ≤
      P.a * (∫ record : Seed × P.experiment.StoppedWord,
        phiReal (P.wordPosteriorError record.2) ∂μ) := by
    calc
      _ ≤ P.rocChord m (∫ record : Seed × P.experiment.StoppedWord,
          P.wordPosteriorError record.2 ∂μ) := rocChord_antitone P m he
      _ = ∫ record : Seed × P.experiment.StoppedWord, P.rocChord m (P.wordPosteriorError record.2) ∂μ :=
        (integral_rocChord P m μ _ hi).symm
      _ ≤ ∫ record : Seed × P.experiment.StoppedWord,
          P.a * phiReal (P.wordPosteriorError record.2) ∂μ :=
        integral_mono (rocChord_integrable P m μ _ hi) (hphi.const_mul P.a)
          (fun record => rocChord_le_wordInformation P m record.2)
      _ = _ := integral_const_mul P.a _
  rw [P.rocPrice_of_pos p hp hh, P.bayesObservationCharge_eq_posteriorInformation ν test hf,
    P.expectedPosteriorInformation_eq_stoppedLaw ν test hf]
  simp_rw [phi_of_pos (P.wordPosteriorError_pos _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hphi
    (ae_of_all _ fun record => phiReal_nonneg (P.wordPosteriorError_pos record.2)
      (P.wordPosteriorError_le_half record.2)), ← ENNReal.ofReal_mul P.a_pos.le]
  exact ENNReal.ofReal_le_ofReal hbound

end PDROC
