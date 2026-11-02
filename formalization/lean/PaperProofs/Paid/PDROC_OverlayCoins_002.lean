module

public import PaperProofs.Paid.PDROC_OverlayCoins_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid

namespace PDROC

universe u

theorem measurable_overlayStageCoinLookup_uncurry :
    Measurable (fun pair : OverlayStageCoins × AuxiliaryRecord =>
      overlayStageCoinLookup pair.1 pair.2) :=
  measurable_from_prod_countable_left (fun record => measurable_overlayStageCoinLookup record)

theorem measurable_overlayCoinTablesLookup (P : Parameters) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : OverlayCoinTables P × AuxiliaryRecord =>
      overlayStageCoinLookup (pair.1 stage) pair.2) := by
  have hm : Measurable (fun pair : OverlayCoinTables P × AuxiliaryRecord =>
      (pair.1 stage, pair.2)) :=
    (((measurable_pi_apply stage).comp measurable_fst).prodMk measurable_snd)
  exact measurable_overlayStageCoinLookup_uncurry.comp hm

theorem measurable_overlaySelectedCoinLookup {X : Type u} [MeasurableSpace X]
    (select : X → AuxiliaryRecord) (hselect : Measurable select) :
    Measurable (fun pair : X × OverlayStageCoins => overlayStageCoinLookup pair.2 (select pair.1)) := by
  exact measurable_overlayStageCoinLookup_uncurry.comp
    (measurable_snd.prodMk (hselect.comp measurable_fst))

theorem measurableSet_overlaySelectedCoinCell {X : Type u} [MeasurableSpace X]
    (select : X → AuxiliaryRecord) (hselect : Measurable select)
    (B : Set X) (hB : MeasurableSet B) (record : AuxiliaryRecord)
    (D : Set ((Bool × Bool) × Bool)) (hD : MeasurableSet D) :
    MeasurableSet {pair : X × OverlayStageCoins | pair.1 ∈ B ∧ select pair.1 = record ∧
      overlayStageCoinLookup pair.2 (select pair.1) ∈ D} := by
  exact (measurable_fst hB).inter
    (((hselect.comp measurable_fst) (measurableSet_singleton record)).inter
      ((measurable_overlaySelectedCoinLookup select hselect) hD))

/-- Full base-variable times selected fresh-coin law on an arbitrary
old-seed/full-entry/record gate. The entire base variable is preserved. -/
theorem overlayStageCoinsLaw_selected_jointLaw {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (mix : AuxiliaryRecord → Measure (Bool × Bool))
    (mark : AuxiliaryRecord → Measure Bool) [∀ record, IsProbabilityMeasure (mix record)]
    [∀ record, IsProbabilityMeasure (mark record)] (select : X → AuxiliaryRecord)
    (hselect : Measurable select) (B : Set X) (hB : MeasurableSet B) (record : AuxiliaryRecord) :
    ((μ.restrict (B ∩ select ⁻¹' {record})).prod (overlayStageCoinsLaw mix mark)).map
        (fun pair => (pair.1, overlayStageCoinLookup pair.2 (select pair.1))) =
      (μ.restrict (B ∩ select ⁻¹' {record})).prod ((mix record).prod (mark record)) := by
  let cell := B ∩ select ⁻¹' {record}
  have hcell : MeasurableSet cell := hB.inter (hselect (measurableSet_singleton record))
  have hseed : ∀ᵐ x ∂μ.restrict cell, select x = record :=
    (ae_restrict_mem hcell).mono (fun _ hx => hx.2)
  have hpair : ∀ᵐ pair ∂(μ.restrict cell).prod (overlayStageCoinsLaw mix mark), select pair.1 = record :=
    (measurePreserving_fst (μ := μ.restrict cell) (ν := overlayStageCoinsLaw mix mark)).quasiMeasurePreserving.ae hseed
  calc
    _ = ((μ.restrict cell).prod (overlayStageCoinsLaw mix mark)).map
        (fun pair => (pair.1, overlayStageCoinLookup pair.2 record)) :=
      Measure.map_congr (hpair.mono fun pair hp => by rw [hp])
    _ = (μ.restrict cell).prod ((mix record).prod (mark record)) := by
      change ((μ.restrict cell).prod (overlayStageCoinsLaw mix mark)).map
        (Prod.map id (fun coins => overlayStageCoinLookup coins record)) = _
      rw [← Measure.map_prod_map _ _ measurable_id (measurable_overlayStageCoinLookup record),
        Measure.map_id, overlayStageCoinsLaw_lookup]

end PDROC
