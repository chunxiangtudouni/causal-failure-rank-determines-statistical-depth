module

public import PaperProofs.Common.HealthyValue
public import PaperProofs.Common.WorldFreshness

/-!
The original independent world restricted and renumbered to the SAME fresh
suffix experiments. This is analysis data, never a controller-visible input.
The exact pushforward laws retain the entire future truth/tape world, empty
suffixes and arbitrary private seed universes. No run/Markov or finite-cost
claim is assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.StatisticalInput

variable {I : Instance}

def restrictFreshWorld (input : StatisticalInput I) :
    (first : Nat) → input.World → (input.freshSuffix first).World
  | 0 => fun world => world
  | first + 1 => fun world stage => world (I.freshStageLift (first + 1) stage)

theorem freshStageLift_injective (I : Instance) (first : Nat) :
    Function.Injective (I.freshStageLift first) := by
  intro left right heq
  apply Fin.ext
  have hh := congrArg Fin.val heq
  change first + left.val = first + right.val at hh
  omega

theorem measurable_restrictFreshWorld (input : StatisticalInput I) (first : Nat) :
    Measurable (input.restrictFreshWorld first) := by
  cases first with
  | zero => exact measurable_id
  | succ first => exact measurable_pi_iff.mpr (fun stage => measurable_pi_apply (I.freshStageLift (first + 1) stage))

theorem restrictFreshWorld_worldLaw (input : StatisticalInput I) (first : Nat) :
    input.worldLaw.map (input.restrictFreshWorld first) = (input.freshSuffix first).worldLaw := by
  cases first with
  | zero => exact Measure.map_id
  | succ first =>
    have hind := ProbabilityTheory.iIndepFun.precomp (freshStageLift_injective I (first + 1))
      input.worldLaw_independent_stages
    change input.worldLaw.map (fun world stage => world (I.freshStageLift (first + 1) stage)) =
      Measure.pi (fun stage => input.stageLaw (I.freshStageLift (first + 1) stage))
    rw [ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun stage => (measurable_pi_apply (I.freshStageLift (first + 1) stage)).aemeasurable) hind]
    congr 1
    funext stage
    exact input.worldLaw_coordinate (I.freshStageLift (first + 1) stage)

theorem lintegral_restrictFreshWorld (input : StatisticalInput I) (first : Nat)
    (f : (input.freshSuffix first).World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ world, f (input.restrictFreshWorld first world) ∂input.worldLaw) =
      ∫⁻ world, f world ∂(input.freshSuffix first).worldLaw := by
  rw [← restrictFreshWorld_worldLaw input first]
  exact (lintegral_map hf (measurable_restrictFreshWorld input first)).symm

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

def restrictFreshSample (input : StatisticalInput I) (first : Nat)
    (sample : Seed × input.World) : Seed × (input.freshSuffix first).World :=
  (sample.1, input.restrictFreshWorld first sample.2)

theorem measurable_restrictFreshSample (input : StatisticalInput I) (first : Nat) :
    Measurable (input.restrictFreshSample (Seed := Seed) first) :=
  measurable_fst.prodMk ((measurable_restrictFreshWorld input first).comp measurable_snd)

theorem restrictFreshSample_seededWorldLaw (input : StatisticalInput I) (first : Nat)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (input.seededWorldLaw ν).map (input.restrictFreshSample first) =
      (input.freshSuffix first).seededWorldLaw ν := by
  have h := Measure.map_prod_map ν input.worldLaw measurable_id (measurable_restrictFreshWorld input first)
  rw [Measure.map_id, restrictFreshWorld_worldLaw] at h
  exact h.symm

theorem lintegral_restrictFreshSample (input : StatisticalInput I) (first : Nat)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : Seed × (input.freshSuffix first).World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample, f (input.restrictFreshSample first sample) ∂input.seededWorldLaw ν) =
      ∫⁻ sample, f sample ∂(input.freshSuffix first).seededWorldLaw ν := by
  rw [← restrictFreshSample_seededWorldLaw input first ν]
  exact (lintegral_map hf (measurable_restrictFreshSample input first)).symm

end PrivateSeed

end PaperProofs.Common.StatisticalInput
