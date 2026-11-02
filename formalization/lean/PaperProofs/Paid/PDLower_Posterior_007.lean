module

public import PaperProofs.Paid.PDLower_Posterior_003
public import PaperProofs.Paid.PDLower_Posterior_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def pastSeedLaw (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee) (ν : Measure Seed)
    (stage : P.sharedInstance.Stage) : Measure (Seed × (P.input fee hf).PastWorld stage) :=
  ((P.input fee hf).seededWorldLaw ν).map ((P.input fee hf).preBirthView stage)

instance pastSeedLaw_probability (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) : IsProbabilityMeasure (pastSeedLaw P fee hf ν stage) := by
  unfold pastSeedLaw
  infer_instance

theorem preBirth_current_jointLaw (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hf).seededWorldLaw ν).map
      (fun sample => ((P.input fee hf).preBirthView stage sample, sample.2 stage)) =
      (pastSeedLaw P fee hf ν stage).prod ((P.input fee hf).stageLaw stage) := by
  have hind := (P.input fee hf).preBirthView_independent_next ν stage
  have hfirst := (P.input fee hf).measurable_preBirthView (Seed := Seed) stage
  have hnext : Measurable (fun sample : Seed × (P.input fee hf).World => sample.2 stage) :=
    (measurable_pi_apply stage).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hfirst.aemeasurable hnext.aemeasurable,
    (P.input fee hf).seededWorldLaw_coordinate]
  rfl

theorem lintegral_preBirth_current (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (f : (Seed × (P.input fee hf).PastWorld stage) × (Bool × P.binarySymmetric.experiment.Tape) → ℝ≥0∞)
    (hF : Measurable f) :
    (∫⁻ sample, f ((P.input fee hf).preBirthView stage sample, sample.2 stage) ∂(P.input fee hf).seededWorldLaw ν) =
      ∑ x : Bool, (1 / 2 : ℝ≥0∞) *
        ∫⁻ sample, f (sample.1, (x, sample.2))
          ∂P.binarySymmetric.experiment.conditionalLaw (pastSeedLaw P fee hf ν stage) x := by
  let joint : Seed × (P.input fee hf).World →
      (Seed × (P.input fee hf).PastWorld stage) × (Bool × P.binarySymmetric.experiment.Tape) :=
    fun sample => ((P.input fee hf).preBirthView stage sample, sample.2 stage)
  have hJ : Measurable joint := ((P.input fee hf).measurable_preBirthView stage).prodMk
    ((measurable_pi_apply stage).comp measurable_snd)
  have hlaw : ((P.input fee hf).seededWorldLaw ν).map joint =
      (pastSeedLaw P fee hf ν stage).prod ((P.input fee hf).stageLaw stage) :=
    preBirth_current_jointLaw P fee hf ν stage
  rw [← lintegral_map hF hJ, hlaw]
  have hlocal (x : Bool) :
      (pastSeedLaw P fee hf ν stage).prod ((Measure.dirac x).prod (P.binarySymmetric.experiment.tapeLaw x)) =
        (P.binarySymmetric.experiment.conditionalLaw (pastSeedLaw P fee hf ν stage) x).map
          (fun sample : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape =>
            (sample.1, (x, sample.2))) := by
    rw [Measure.dirac_prod]
    have hg : Measurable (fun tape : P.binarySymmetric.experiment.Tape => (x, tape)) :=
      measurable_const.prodMk measurable_id
    have h := Measure.map_prod_map (pastSeedLaw P fee hf ν stage) (P.binarySymmetric.experiment.tapeLaw x) measurable_id hg
    have hmap : Prod.map (id : (Seed × (P.input fee hf).PastWorld stage) → (Seed × (P.input fee hf).PastWorld stage))
        (fun tape : P.binarySymmetric.experiment.Tape => (x, tape)) =
        (fun sample : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape =>
          (sample.1, (x, sample.2))) := rfl
    rw [Measure.map_id, hmap] at h
    exact h
  change (∫⁻ data, f data ∂(pastSeedLaw P fee hf ν stage).prod
    (P.binarySymmetric.experiment.priorMass true • (Measure.dirac true).prod (P.binarySymmetric.experiment.tapeLaw true) +
      P.binarySymmetric.experiment.priorMass false • (Measure.dirac false).prod (P.binarySymmetric.experiment.tapeLaw false))) = _
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [hlocal, lintegral_map hF (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)),
    Fintype.sum_bool, P.binarySymmetric.priorMass_eq_half, smul_eq_mul]

end PDLower
