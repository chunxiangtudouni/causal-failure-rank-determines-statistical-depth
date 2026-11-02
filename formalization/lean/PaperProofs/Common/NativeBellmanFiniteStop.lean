module

public import PaperProofs.Common.NativeHeadBayes
public import PaperProofs.Common.NativeBellmanUpper

/-!
Finite stopping of the chosen local rule is derived on the original whole
world law from its finite extended Bayes objective. It is not a restriction
on the full-policy comparator or an assumption of Bellman upper assembly.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

theorem localTest_finiteStop_seededWorld (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : (input.experiment stage).AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : (input.experiment stage).bayesObjective ν test penalty ≠ ⊤) :
    ∀ᵐ sample ∂input.seededWorldLaw ν,
      test.rule.stop sample.1 (worldTapes input sample.2 stage) ≠ ⊤ := by
  have hobs : (input.experiment stage).bayesObservationCharge ν test ≠ ⊤ := by
    intro htop
    apply hfinite
    exact top_le_iff.mp (htop ▸ (le_self_add :
      (input.experiment stage).bayesObservationCharge ν test ≤
        (input.experiment stage).bayesObjective ν test penalty))
  rw [bayesObservationCharge_eq_seededWorld_integral input stage ν test] at hobs
  have hlocal : Measurable (fun sample : Seed × input.World =>
      (sample.1, worldTapes input sample.2 stage)) :=
    measurable_fst.prodMk (((measurable_pi_apply stage).comp measurable_snd).snd)
  have hm : Measurable (fun sample : Seed × input.World =>
      (input.experiment stage).observationCharge
        (test.rule.stop sample.1 (worldTapes input sample.2 stage))) :=
    (measurable_of_countable (input.experiment stage).observationCharge).comp
      (test.measurable_stop.comp hlocal)
  filter_upwards [ae_lt_top hm hobs] with sample hs
  intro htop
  simp only [htop, BinaryExperiment.observationCharge_top, lt_self_iff_false] at hs

theorem localTest_exists_stop_seededWorld (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : (input.experiment stage).AdmissibleRule Seed) (penalty : ℝ≥0∞)
    (hfinite : (input.experiment stage).bayesObjective ν test penalty ≠ ⊤) :
    ∀ᵐ sample ∂input.seededWorldLaw ν, ∃ n : ℕ,
      test.rule.stop sample.1 (worldTapes input sample.2 stage) = n := by
  filter_upwards [localTest_finiteStop_seededWorld input stage ν test penalty hfinite] with sample hs
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hs
  exact ⟨n, hn.symm⟩

end PaperProofs.Common.Native
