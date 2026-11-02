module

public import PaperProofs.Paid.BSCAdapter
public import PaperProofs.Common.World

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem paid_stage_truth_mass (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (truth : Bool) :
    (P.input fee hf).stageLaw stage {sample | sample.1 = truth} = (1 / 2 : ℝ≥0∞) := by
  have heq : {sample : (P.input fee hf).StageSample stage | sample.1 = truth} =
      ({truth} ×ˢ (Set.univ : Set ((P.input fee hf).experiment stage).Tape)) := by
    ext sample
    change (sample.1 = truth) ↔ ((sample.1 = truth) ∧ True)
    simp only [and_true]
  rw [heq, StatisticalInput.stageLaw_truth_tape, measure_univ, mul_one]
  change P.experiment.priorMass truth = _
  rw [P.experiment_eq_binarySymmetric]
  simp only [BinaryExperiment.priorMass, BinaryExperiment.priorReal,
    P.binarySymmetric.prior_eq_half]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem paid_truth_assignment_mass (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (truth : P.sharedInstance.Stage → Bool) :
    (P.input fee hf).worldLaw {world | (P.input fee hf).truthAt world = truth} =
      ENNReal.ofReal (((1 / 2 : ℚ) ^ P.certificate.stages : ℚ) : ℝ) := by
  have heq : {world : (P.input fee hf).World | (P.input fee hf).truthAt world = truth} =
      Set.pi Set.univ (fun stage => {sample : (P.input fee hf).StageSample stage | sample.1 = truth stage}) := by
    ext world
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    exact funext_iff
  rw [heq, StatisticalInput.worldLaw, Measure.pi_pi]
  simp_rw [paid_stage_truth_mass]
  have hcard : Fintype.card P.sharedInstance.Stage = P.certificate.stages := by
    simp only [Parameters.sharedInstance, Instance.Stage, List.length_replicate, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ, hcard]
  rw [Rat.cast_pow, ENNReal.ofReal_pow (by norm_num)]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end PDLower
