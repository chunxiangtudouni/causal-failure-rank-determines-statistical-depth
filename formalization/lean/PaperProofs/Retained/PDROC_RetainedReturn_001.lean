module

public import PaperProofs.Retained.PRet_RiskMassFlow_Realization_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained
open PaperProofs.Statistics MeasureTheory

namespace PDROC.RetainedReturn

variable {I : Instance}

theorem posteriorStop_ae_finite (E : BinaryExperiment) (p : ℚ)
    (positive : 0 < p) (small : p ≤ 1 / 4) (truth : Bool) :
    ∀ᵐ tape ∂E.tapeLaw truth, E.posteriorThresholdStop p tape ≠ ⊤ := by
  have finite := E.expectedSamples_finite_stop (Measure.dirac ()) (E.posteriorSPRT p) truth
    (E.posteriorSPRT_expectedSamples_finite p
      (BinaryExperiment.posteriorThreshold_nonneg p positive small) truth)
  have measurable : MeasurableSet {tape | E.posteriorThresholdStop p tape ≠ ⊤} :=
    (measurableSet_singleton (⊤ : ℕ∞)).compl.preimage
      (E.measurable_posteriorThresholdStop p)
  have mapped : (E.conditionalLaw (Measure.dirac ()) truth).map Prod.snd = E.tapeLaw truth := by
    simp only [BinaryExperiment.conditionalLaw, Measure.map_snd_prod, measure_univ, one_smul]
  rw [← mapped]
  apply (ae_map_iff measurable_snd.aemeasurable measurable).mpr
  exact finite

theorem stage_posteriorStop_ae_finite (input : StatisticalInput I) (stage : I.Stage)
    (p : ℚ) (positive : 0 < p) (small : p ≤ 1 / 4) :
    ∀ᵐ sample ∂input.stageLaw stage,
      (input.experiment stage).posteriorThresholdStop p sample.2 ≠ ⊤ := by
  have conditional (truth : Bool) :
      ∀ᵐ sample ∂(Measure.dirac truth).prod ((input.experiment stage).tapeLaw truth),
        (input.experiment stage).posteriorThresholdStop p sample.2 ≠ ⊤ := by
    have mapped : ∀ᵐ tape ∂((Measure.dirac truth).prod
        ((input.experiment stage).tapeLaw truth)).map Prod.snd,
        (input.experiment stage).posteriorThresholdStop p tape ≠ ⊤ := by
      simpa only [Measure.map_snd_prod, measure_univ, one_smul] using
        posteriorStop_ae_finite (input.experiment stage) p positive small truth
    exact ae_of_ae_map (f := fun sample : Bool × (input.experiment stage).Tape => sample.2)
      measurable_snd.aemeasurable mapped
  rw [StatisticalInput.stageLaw]
  exact ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure (conditional true) _,
    Measure.ae_smul_measure (conditional false) _⟩

theorem seeded_posteriorStop_ae_finite (input : StatisticalInput I) (stage : I.Stage)
    (p : ℚ) (positive : 0 < p) (small : p ≤ 1 / 4) :
    ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
      (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 ≠ ⊤ := by
  have mapped : ∀ᵐ localSample ∂(input.seededWorldLaw (Measure.dirac ())).map
      (fun sample : Unit × input.World => sample.2 stage),
      (input.experiment stage).posteriorThresholdStop p localSample.2 ≠ ⊤ := by
    rw [input.seededWorldLaw_coordinate]
    exact stage_posteriorStop_ae_finite input stage p positive small
  exact ae_of_ae_map (f := fun sample : Unit × input.World => sample.2 stage)
    ((measurable_pi_apply stage).comp measurable_snd).aemeasurable mapped

/-- All valid rational targets are covered on one full-measure set. The
actual entry target may depend on the entire visible earlier-stage record. -/
theorem all_posteriorStops_ae_finite (input : StatisticalInput I) :
    ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
      ∀ (stage : I.Stage) (p : ℚ), 0 < p → p ≤ 1 / 4 →
        (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 ≠ ⊤ := by
  apply ae_all_iff.mpr
  intro stage
  apply ae_all_iff.mpr
  intro p
  by_cases positive : 0 < p
  · by_cases small : p ≤ 1 / 4
    · filter_upwards [seeded_posteriorStop_ae_finite input stage p positive small] with sample finite
      exact fun _ _ => finite
    · exact ae_of_all _ (fun _ _ bound => (small bound).elim)
  · exact ae_of_all _ (fun _ bound _ => (positive bound).elim)

end PDROC.RetainedReturn
