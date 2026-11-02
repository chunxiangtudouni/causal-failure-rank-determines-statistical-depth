module

public import PaperProofs.Common.Model
public import PaperProofs.Statistics.Experiment

/-!
One common statistical input: channel observation prices and actual-execution
accounting prices are derived from the same data, rather than copied assumptions.
World and NativeExecution supply the stochastic native execution semantics;
this light input module introduces no controller performance assumptions.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common

structure StatisticalInput (I : Instance) where
  experiment : I.Stage → Statistics.BinaryExperiment
  correctionFee : I.Stage → I.Tool → ℚ
  correctionFee_nonneg : ∀ i r, 0 ≤ correctionFee i r

def StatisticalInput.fees {I : Instance} (input : StatisticalInput I) : Fees I where
  observation i := (input.experiment i).observationFee
  observation_pos i := (input.experiment i).observationFee_pos
  correction := input.correctionFee
  correction_nonneg := input.correctionFee_nonneg

theorem StatisticalInput.observationFee_agrees {I : Instance} (input : StatisticalInput I)
    (i : I.Stage) : input.fees.observation i = (input.experiment i).observationFee := rfl

/-- The local sequential-test bill is exactly the same charge used by global ledgers,
including an infinite observation count. -/
theorem StatisticalInput.observationCharge_agrees {I : Instance} (input : StatisticalInput I)
    (i : I.Stage) (samples : ℕ∞) :
    (input.experiment i).observationCharge samples =
      ENNReal.ofReal (input.fees.observation i : ℝ) * (samples : ℝ≥0∞) := by
  change (input.experiment i).observationCharge samples =
    ENNReal.ofReal ((input.experiment i).observationFee : ℝ) * (samples : ℝ≥0∞)
  by_cases hinfinite : samples = ⊤
  · subst samples
    have hfee : ENNReal.ofReal ((input.experiment i).observationFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (input.experiment i).observationFee_real_pos)
    simp [hfee]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hinfinite
    rw [← hn]
    simp

end PaperProofs.Common
