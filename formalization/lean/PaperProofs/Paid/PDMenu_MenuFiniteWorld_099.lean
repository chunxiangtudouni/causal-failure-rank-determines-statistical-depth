module

public import PaperProofs.Paid.PDMenu_MenuFramedEndpoint_094
public import PaperProofs.Paid.PDROC_EndpointFinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menu_fresh_worldTape_map (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : (freshInstance N K).Stage) :
    (P.freshInput N K fee hfee).worldLaw.map
      (fun world => worldTapes (P.freshInput N K fee hfee) world stage) = PDROC.auxiliaryTapeLaw P := by
  rw [PDROC.worldTape_map]
  change PDROC.experimentTapeMixture P.binarySymmetric.experiment = _
  unfold PDROC.experimentTapeMixture PDROC.auxiliaryTapeLaw
  rw [P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  exact add_comm _ _

universe u

/-- A single original probability-one set contains all levels, both coins
and every physical stage. Adaptive selection of the actual table cell does
not add an independence or finite-runtime premise. -/
theorem menu_allEndpoints_finite_seededWorld (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ sample ∂(P.freshInput N K fee hfee).seededWorldLaw ν,
      ∀ (stage : (freshInstance N K).Stage) (level : ℕ) (coin : Bool), ∃ reviews : ℕ,
        (menuAnalysisTest P level).rule.stop coin
          (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews := by
  have hworld (stage : (freshInstance N K).Stage) :
      ∀ᵐ world ∂(P.freshInput N K fee hfee).worldLaw,
        PDROC.FiniteEndpointTape P.binarySymmetric (worldTapes (P.freshInput N K fee hfee) world stage) := by
    have hmap : ∀ᵐ tape ∂((P.freshInput N K fee hfee).worldLaw.map
        (fun world => worldTapes (P.freshInput N K fee hfee) world stage)), PDROC.FiniteEndpointTape P.binarySymmetric tape := by
      rw [menu_fresh_worldTape_map]
      exact PDROC.finiteEndpointTape_auxiliaryLaw P
    exact (ae_map_iff (PDROC.measurable_worldTape (P.freshInput N K fee hfee) stage).aemeasurable
      (PDROC.measurableSet_finiteEndpointTape P.binarySymmetric)).mp hmap
  have hmap : ((P.freshInput N K fee hfee).seededWorldLaw ν).map Prod.snd = (P.freshInput N K fee hfee).worldLaw := by
    change (ν.prod (P.freshInput N K fee hfee).worldLaw).map Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hseed (stage : (freshInstance N K).Stage) :
      ∀ᵐ sample ∂(P.freshInput N K fee hfee).seededWorldLaw ν,
        PDROC.FiniteEndpointTape P.binarySymmetric (worldTapes (P.freshInput N K fee hfee) sample.2 stage) := by
    have hm : ∀ᵐ world ∂(((P.freshInput N K fee hfee).seededWorldLaw ν).map Prod.snd),
        PDROC.FiniteEndpointTape P.binarySymmetric (worldTapes (P.freshInput N K fee hfee) world stage) := by
      rw [hmap]
      exact hworld stage
    exact ae_of_ae_map (μ := (P.freshInput N K fee hfee).seededWorldLaw ν) measurable_snd.aemeasurable hm
  filter_upwards [ae_all_iff.mpr hseed] with sample hs
  intro stage level coin
  obtain ⟨reviews, hreviews⟩ := ENat.ne_top_iff_exists.mp (hs stage level coin)
  exact ⟨reviews, hreviews.symm⟩

end PDMenu
