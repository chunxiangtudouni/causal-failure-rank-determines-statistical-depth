module

public import PaperProofs.Statistics.PDROC_ExactROC_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootBSCEndpointPenalty

open PaperProofs.Statistics PaperProofs.Statistics.BinarySymmetric

noncomputable def endpointInf (P : Parameters) (d : ℝ) : ℝ≥0∞ :=
  ⨅ m : ℕ, ENNReal.ofReal (P.endpointCharge m : ℝ) +
    ENNReal.ofReal d * ENNReal.ofReal (P.endpointError m : ℝ)

theorem endpointInf_le_roc (P : Parameters) (d : ℝ) (hd : 0 ≤ d)
    (p : ℝ) (hp : 0 < p) (hh : p ≤ 1 / 2) :
    endpointInf P d ≤ P.rocPrice p + ENNReal.ofReal d * ENNReal.ofReal p := by
  let m := P.rocIndex p hp
  let w := P.rocWeight m p
  have hw : 0 ≤ w ∧ w ≤ 1 := P.rocWeight_mem_Icc m p (P.rocIndex_lower p hp) (P.rocIndex_upper p hp hh)
  have hc (n : ℕ) : 0 ≤ (P.endpointCharge n : ℝ) := by exact_mod_cast P.endpointCharge_nonneg n
  have he (n : ℕ) : 0 ≤ (P.endpointError n : ℝ) := by exact_mod_cast (P.endpointError_pos n).le
  have rewrite_endpoint (n : ℕ) :
      ENNReal.ofReal (P.endpointCharge n : ℝ) + ENNReal.ofReal d * ENNReal.ofReal (P.endpointError n : ℝ) =
        ENNReal.ofReal ((P.endpointCharge n : ℝ) + d * (P.endpointError n : ℝ)) := by
    rw [← ENNReal.ofReal_mul hd, ENNReal.ofReal_add (hc n) (mul_nonneg hd (he n))]
  let left := (P.endpointCharge m : ℝ) + d * (P.endpointError m : ℝ)
  let right := (P.endpointCharge (m + 1) : ℝ) + d * (P.endpointError (m + 1) : ℝ)
  have hleft := mul_le_mul_of_nonneg_left (min_le_left left right) hw.1
  have hright := mul_le_mul_of_nonneg_left (min_le_right left right) (sub_nonneg.mpr hw.2)
  have hi := P.rocWeight_error_interpolation m p
  have hdi := congrArg (fun z : ℝ => d * z) hi
  have hmin : min left right ≤ P.rocChord m p + d * p := by
    dsimp [left, right, w] at hleft hright ⊢
    unfold Parameters.rocChord
    nlinarith only [hleft, hright, hdi]
  have hchord : 0 ≤ P.rocChord m p :=
    P.rocChord_nonneg m p (P.rocIndex_lower p hp) (P.rocIndex_upper p hp hh)
  have hbound (n : ℕ) : endpointInf P d ≤
      ENNReal.ofReal ((P.endpointCharge n : ℝ) + d * (P.endpointError n : ℝ)) := by
    calc
      endpointInf P d ≤ ENNReal.ofReal (P.endpointCharge n : ℝ) +
          ENNReal.ofReal d * ENNReal.ofReal (P.endpointError n : ℝ) := iInf_le _ n
      _ = _ := rewrite_endpoint n
  calc
    endpointInf P d ≤ min (ENNReal.ofReal left) (ENNReal.ofReal right) := by
      apply le_min
      · exact hbound m
      · exact hbound (m + 1)
    _ = ENNReal.ofReal (min left right) := (ENNReal.ofReal_min _ _).symm
    _ ≤ ENNReal.ofReal (P.rocChord m p + d * p) := ENNReal.ofReal_le_ofReal hmin
    _ = P.rocPrice p + ENNReal.ofReal d * ENNReal.ofReal p := by
      rw [P.rocPrice_of_pos p hp hh, ENNReal.ofReal_add hchord (mul_nonneg hd hp.le), ENNReal.ofReal_mul hd]

universe u

set_option maxHeartbeats 800000 in
theorem adjustedBayesError_pos_of_finite {Seed : Type u} [MeasurableSpace Seed]
    (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) (d : ℝ≥0∞)
    (hf : P.experiment.bayesObjective ν test d ≠ ⊤) :
    0 < P.adjustedBayesError ν test := by
  have hcounts := P.experiment.bayesObjective_finite_expectedSamples ν test d hf
  let μ : Measure (Seed × P.experiment.StoppedWord) := P.bayesStoppedLaw ν test
  let f : (Seed × P.experiment.StoppedWord) → ℝ := fun record => P.wordPosteriorError record.2
  let _ : IsProbabilityMeasure μ := _root_.PDROC.bayesStoppedLaw_probability P ν test
  have hi : Integrable f μ := _root_.PDROC.posteriorError_integrable P ν test
  have hpos : 0 < ∫ record, f record ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (μ := μ) (f := f)
      (fun record => (P.wordPosteriorError_pos record.2).le) hi).mpr
    have hs : Function.support f = Set.univ := by
      ext record
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (P.wordPosteriorError_pos record.2).ne'
    rw [hs, measure_univ]
    exact zero_lt_one
  exact hpos.trans_le (_root_.PDROC.integral_posteriorError_le_adjusted P ν test hcounts)

theorem endpointInf_le_bayesObjective_any_seed {Seed : Type u} [MeasurableSpace Seed]
    (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) (d : ℝ) (hd : 0 ≤ d) :
    endpointInf P d ≤ P.experiment.bayesObjective ν test (ENNReal.ofReal d) := by
  by_cases hf : P.experiment.bayesObjective ν test (ENNReal.ofReal d) = ⊤
  · rw [hf]
    exact le_top
  have hp := adjustedBayesError_pos_of_finite P ν test (ENNReal.ofReal d) hf
  have hh := (P.adjustedBayesError_mem_Icc ν test).2
  have he : 0 < (P.rocBayesError ν test).val := lt_of_lt_of_le hp (min_le_left _ _)
  have heone : (P.rocBayesError ν test).val < 1 := by
    have h := lt_of_lt_of_le hp (min_le_right (P.rocBayesError ν test).val (1 - (P.rocBayesError ν test).val))
    linarith
  have hroc := (PaperProofs.Statistics.PDROC.exactROCClaims P).1 Seed inferInstance ν inferInstance test he heone
  have herror : ENNReal.ofReal (P.adjustedBayesError ν test) ≤ P.experiment.bayesError ν test := by
    rw [← P.rocBayesError_exact ν test]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  exact (endpointInf_le_roc P d hd _ hp hh).trans
    (add_le_add hroc (by simpa only [mul_comm] using mul_le_mul_left herror (ENNReal.ofReal d)))

end RootBSCEndpointPenalty
