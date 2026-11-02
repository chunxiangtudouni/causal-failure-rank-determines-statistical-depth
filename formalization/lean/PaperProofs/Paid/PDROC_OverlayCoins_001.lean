module

public import PaperProofs.Paid.RepresentationClaims
public import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid

namespace PDROC

universe u

/-- A complete private row of independent coins, indexed by the sampled
auxiliary record. Lookup uses a record known before any current fresh coin. -/
abbrev OverlayStageCoins :=
  (AuxiliaryRecord → Bool × Bool) × (AuxiliaryRecord → Bool)

abbrev OverlayCoinTables (P : Parameters) := P.sharedInstance.Stage → OverlayStageCoins

def overlayStageCoinLookup (coins : OverlayStageCoins) (record : AuxiliaryRecord) :
    (Bool × Bool) × Bool := (coins.1 record, coins.2 record)

theorem measurable_overlayStageCoinLookup (record : AuxiliaryRecord) :
    Measurable (fun coins : OverlayStageCoins => overlayStageCoinLookup coins record) :=
  ((measurable_pi_apply record).comp measurable_fst).prodMk
    ((measurable_pi_apply record).comp measurable_snd)

/-- Mathlib's arbitrary product probability measure supplies the countable
record tables; no finite support or bounded record assumption is required. -/
noncomputable def overlayStageCoinsLaw (mix : AuxiliaryRecord → Measure (Bool × Bool))
    (mark : AuxiliaryRecord → Measure Bool) : Measure OverlayStageCoins :=
  (Measure.infinitePi mix).prod (Measure.infinitePi mark)

instance overlayStageCoinsLaw_probability (mix : AuxiliaryRecord → Measure (Bool × Bool))
    (mark : AuxiliaryRecord → Measure Bool) [∀ record, IsProbabilityMeasure (mix record)]
    [∀ record, IsProbabilityMeasure (mark record)] :
    IsProbabilityMeasure (overlayStageCoinsLaw mix mark) := by
  unfold overlayStageCoinsLaw
  infer_instance

noncomputable def overlayCoinTablesLaw (P : Parameters)
    (mix : AuxiliaryRecord → Measure (Bool × Bool)) (mark : AuxiliaryRecord → Measure Bool) :
    Measure (OverlayCoinTables P) :=
  Measure.pi (fun _ : P.sharedInstance.Stage => overlayStageCoinsLaw mix mark)

instance overlayCoinTablesLaw_probability (P : Parameters)
    (mix : AuxiliaryRecord → Measure (Bool × Bool)) (mark : AuxiliaryRecord → Measure Bool)
    [∀ record, IsProbabilityMeasure (mix record)] [∀ record, IsProbabilityMeasure (mark record)] :
    IsProbabilityMeasure (overlayCoinTablesLaw P mix mark) := by
  unfold overlayCoinTablesLaw
  infer_instance

theorem overlayStageCoinsLaw_lookup (mix : AuxiliaryRecord → Measure (Bool × Bool))
    (mark : AuxiliaryRecord → Measure Bool) [∀ record, IsProbabilityMeasure (mix record)]
    [∀ record, IsProbabilityMeasure (mark record)] (record : AuxiliaryRecord) :
    (overlayStageCoinsLaw mix mark).map (fun coins => overlayStageCoinLookup coins record) =
      (mix record).prod (mark record) := by
  unfold overlayStageCoinsLaw overlayStageCoinLookup
  change ((Measure.infinitePi mix).prod (Measure.infinitePi mark)).map
    (Prod.map (fun f => f record) (fun f => f record)) = _
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply record) (measurable_pi_apply record),
    Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]

theorem overlayCoinTablesLaw_stage (P : Parameters)
    (mix : AuxiliaryRecord → Measure (Bool × Bool)) (mark : AuxiliaryRecord → Measure Bool)
    [∀ record, IsProbabilityMeasure (mix record)] [∀ record, IsProbabilityMeasure (mark record)]
    (stage : P.sharedInstance.Stage) :
    (overlayCoinTablesLaw P mix mark).map (fun coins => coins stage) = overlayStageCoinsLaw mix mark :=
  (measurePreserving_eval (fun _ : P.sharedInstance.Stage => overlayStageCoinsLaw mix mark) stage).map_eq

theorem overlayCoinTablesLaw_lookup (P : Parameters)
    (mix : AuxiliaryRecord → Measure (Bool × Bool)) (mark : AuxiliaryRecord → Measure Bool)
    [∀ record, IsProbabilityMeasure (mix record)] [∀ record, IsProbabilityMeasure (mark record)]
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    (overlayCoinTablesLaw P mix mark).map (fun coins => overlayStageCoinLookup (coins stage) record) =
      (mix record).prod (mark record) := by
  change (overlayCoinTablesLaw P mix mark).map
    ((fun coins : OverlayStageCoins => overlayStageCoinLookup coins record) ∘
      (fun coins : OverlayCoinTables P => coins stage)) = _
  rw [← Measure.map_map (measurable_overlayStageCoinLookup record) (measurable_pi_apply stage),
    overlayCoinTablesLaw_stage, overlayStageCoinsLaw_lookup]

/-- An arbitrary measurable old-seed/full-entry/record gate retains the exact
fresh record-indexed coin law. The gate cannot inspect the current fresh row. -/
theorem overlayStageCoinsLaw_selected_cell {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (mix : AuxiliaryRecord → Measure (Bool × Bool))
    (mark : AuxiliaryRecord → Measure Bool) [∀ record, IsProbabilityMeasure (mix record)]
    [∀ record, IsProbabilityMeasure (mark record)] (select : X → AuxiliaryRecord)
    (B : Set X) (record : AuxiliaryRecord) (D : Set ((Bool × Bool) × Bool)) (hD : MeasurableSet D) :
    (μ.prod (overlayStageCoinsLaw mix mark))
        {pair | pair.1 ∈ B ∧ select pair.1 = record ∧ overlayStageCoinLookup pair.2 (select pair.1) ∈ D} =
      μ (B ∩ select ⁻¹' {record}) * ((mix record).prod (mark record)) D := by
  have hset :
      {pair : X × OverlayStageCoins | pair.1 ∈ B ∧ select pair.1 = record ∧
          overlayStageCoinLookup pair.2 (select pair.1) ∈ D} =
        (B ∩ select ⁻¹' {record}) ×ˢ ((fun coins => overlayStageCoinLookup coins record) ⁻¹' D) := by
    ext pair
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hr, hd⟩
      exact ⟨⟨hb, hr⟩, by simpa only [hr] using hd⟩
    · rintro ⟨⟨hb, hr⟩, hd⟩
      exact ⟨hb, hr, by simpa only [hr] using hd⟩
  rw [hset, Measure.prod_prod]
  rw [← Measure.map_apply (measurable_overlayStageCoinLookup record) hD,
    overlayStageCoinsLaw_lookup]

end PDROC
