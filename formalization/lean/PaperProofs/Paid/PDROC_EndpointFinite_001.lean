module

public import PaperProofs.Paid.PDROC_LocalRecord_005
public import PaperProofs.Statistics.PDROC_Mixture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

def FiniteEndpointTape (P : PaperProofs.Statistics.BinarySymmetric.Parameters) (tape : P.experiment.Tape) : Prop :=
  ∀ (m : ℕ) (coin : Bool), (P.rocEndpointTest m).rule.stop coin tape ≠ ⊤

theorem measurableSet_finiteEndpointTape (P : PaperProofs.Statistics.BinarySymmetric.Parameters) :
    MeasurableSet {tape | FiniteEndpointTape P tape} := by
  simp only [FiniteEndpointTape, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro coin
  exact (((P.rocEndpointTest m).measurable_stop.comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton (⊤ : ℕ∞))).compl

theorem endpoint_finite_tapeLaw (P : PaperProofs.Statistics.BinarySymmetric.Parameters) (m : ℕ) (coin actualTruth : Bool) :
    ∀ᵐ tape ∂P.experiment.tapeLaw actualTruth, (P.rocEndpointTest m).rule.stop coin tape ≠ ⊤ := by
  by_cases hm : m = 0
  · subst m
    exact ae_of_all _ fun _ => by simp [rocEndpointTest, fairGuessTest]
  · have hf := P.experiment.expectedSamples_finite_stop (Measure.dirac ()) (P.symmetricHittingTest m)
      actualTruth (P.symmetricHittingTest_expectedSamples_finite m actualTruth)
    have hp : ∀ᵐ seedUnit ∂(Measure.dirac ()), ∀ᵐ tape ∂P.experiment.tapeLaw actualTruth,
        (P.symmetricHittingTest m).rule.stop seedUnit tape ≠ ⊤ := Measure.ae_ae_of_ae_prod hf
    have hmeas : MeasurableSet {seedUnit : Unit | ∀ᵐ tape ∂P.experiment.tapeLaw actualTruth,
        (P.symmetricHittingTest m).rule.stop seedUnit tape ≠ ⊤} := (Set.toFinite _).measurableSet
    have ht : ∀ᵐ tape ∂P.experiment.tapeLaw actualTruth,
        (P.symmetricHittingTest m).rule.stop () tape ≠ ⊤ := (ae_dirac_iff hmeas).mp hp
    filter_upwards [ht] with tape hs
    simpa only [rocEndpointTest, hm, ↓reduceIte, hittingTestOnBool] using hs

theorem finiteEndpointTape_tapeLaw (P : PaperProofs.Statistics.BinarySymmetric.Parameters) (actualTruth : Bool) :
    ∀ᵐ tape ∂P.experiment.tapeLaw actualTruth, FiniteEndpointTape P tape := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro coin
  exact endpoint_finite_tapeLaw P m coin actualTruth

theorem finiteEndpointTape_auxiliaryLaw (P : PaperProofs.Paid.Parameters) :
    ∀ᵐ tape ∂auxiliaryTapeLaw P, FiniteEndpointTape P.binarySymmetric tape := by
  unfold auxiliaryTapeLaw
  exact ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure (finiteEndpointTape_tapeLaw P.binarySymmetric false) _,
      Measure.ae_smul_measure (finiteEndpointTape_tapeLaw P.binarySymmetric true) _⟩

theorem paid_worldTape_map_auxiliaryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage) :
    (P.input fee hfee).worldLaw.map (fun world => worldTapes (P.input fee hfee) world stage) = auxiliaryTapeLaw P := by
  rw [worldTape_map]
  change experimentTapeMixture P.binarySymmetric.experiment = _
  unfold experimentTapeMixture auxiliaryTapeLaw
  rw [P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  exact add_comm _ _

theorem finiteEndpointTape_world (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage) :
    ∀ᵐ world ∂(P.input fee hfee).worldLaw,
      FiniteEndpointTape P.binarySymmetric (worldTapes (P.input fee hfee) world stage) := by
  have ht : ∀ᵐ tape ∂((P.input fee hfee).worldLaw.map
      (fun world => worldTapes (P.input fee hfee) world stage)), FiniteEndpointTape P.binarySymmetric tape := by
    rw [paid_worldTape_map_auxiliaryLaw]
    exact finiteEndpointTape_auxiliaryLaw P
  exact (ae_map_iff (measurable_worldTape (P.input fee hfee) stage).aemeasurable
    (measurableSet_finiteEndpointTape P.binarySymmetric)).mp ht

universe u

theorem finiteEndpointTape_seededWorld (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) {Seed : Type u} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      FiniteEndpointTape P.binarySymmetric (worldTapes (P.input fee hfee) sample.2 stage) := by
  have hmap : ((P.input fee hfee).seededWorldLaw ν).map Prod.snd = (P.input fee hfee).worldLaw := by
    change (ν.prod (P.input fee hfee).worldLaw).map Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hset : MeasurableSet {world : (P.input fee hfee).World |
      FiniteEndpointTape P.binarySymmetric (worldTapes (P.input fee hfee) world stage)} :=
    (measurableSet_finiteEndpointTape P.binarySymmetric).preimage (measurable_worldTape (P.input fee hfee) stage)
  have hworld : ∀ᵐ world ∂(((P.input fee hfee).seededWorldLaw ν).map Prod.snd),
      FiniteEndpointTape P.binarySymmetric (worldTapes (P.input fee hfee) world stage) := by
    rw [hmap]
    exact finiteEndpointTape_world P fee hfee stage
  exact (ae_map_iff measurable_snd.aemeasurable hset).mp hworld

/-- All stages, all levels and both private tie coins stop on the same
measure-one world set. A level selected from the seed/history may therefore
be substituted without an independence premise or a finite-ET input. -/
theorem allEndpoints_finite_seededWorld (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) {Seed : Type u} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
        (P.binarySymmetric.rocEndpointTest m).rule.stop coin
          (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞) := by
  have ha : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      ∀ stage, FiniteEndpointTape P.binarySymmetric (worldTapes (P.input fee hfee) sample.2 stage) :=
    ae_all_iff.mpr (fun stage => finiteEndpointTape_seededWorld P fee hfee ν stage)
  filter_upwards [ha] with sample hs
  intro stage m coin
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hs stage m coin)
  exact ⟨n, hn.symm⟩

end PDROC
