module

public import PaperProofs.Paid.PDROC_SimulatorCells_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDROC

universe u v w

variable {Sample : Type u} {Gate : Type v} {Fresh : Type w}
    [MeasurableSpace Sample] [MeasurableSpace Gate] [MeasurableSpace Fresh]

theorem productGate_preimage_mass (μ : Measure Sample) (ρ : Measure Gate) (ε : Measure Fresh)
    [IsProbabilityMeasure ε] (joint : Sample → Gate × Fresh) (hj : Measurable joint)
    (hlaw : μ.map joint = ρ.prod ε) (D : Set Gate) (hD : MeasurableSet D) :
    μ (joint ⁻¹' (D ×ˢ Set.univ)) = ρ D := by
  rw [← Measure.map_apply hj (hD.prod MeasurableSet.univ), hlaw, Measure.prod_prod, measure_univ, mul_one]

theorem productGate_cell_lintegral (μ : Measure Sample) (ρ : Measure Gate) (ε : Measure Fresh)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ε]
    (joint : Sample → Gate × Fresh) (hj : Measurable joint) (hlaw : μ.map joint = ρ.prod ε)
    (D : Set Gate) (hD : MeasurableSet D) (cell : Set Sample)
    (hcell : cell = joint ⁻¹' (D ×ˢ Set.univ))
    (bill : Sample → ℝ≥0∞) (charge : Fresh → ℝ≥0∞) (hc : Measurable charge)
    (hbill : ∀ᵐ sample ∂μ, sample ∈ cell → bill sample = charge (joint sample).2) :
    (∫⁻ sample, cell.indicator bill sample ∂μ) = (∫⁻ fresh, charge fresh ∂ε) * μ cell := by
  let model := (D ×ˢ Set.univ).indicator (fun pair : Gate × Fresh => charge pair.2)
  have hm : Measurable model := (hc.comp measurable_snd).indicator (hD.prod MeasurableSet.univ)
  have heq : (fun sample => cell.indicator bill sample) =ᵐ[μ] (fun sample => model (joint sample)) := by
    filter_upwards [hbill] with sample hs
    have hi : sample ∈ cell ↔ joint sample ∈ D ×ˢ Set.univ := by rw [hcell]; rfl
    by_cases hb : sample ∈ cell
    · rw [Set.indicator_of_mem hb, show model (joint sample) = charge (joint sample).2 from
        Set.indicator_of_mem (hi.mp hb) _]
      exact hs hb
    · rw [Set.indicator_of_notMem hb, show model (joint sample) = 0 from
        Set.indicator_of_notMem (fun h => hb (hi.mpr h)) _]
  calc
    _ = ∫⁻ sample, model (joint sample) ∂μ := lintegral_congr_ae heq
    _ = ∫⁻ pair, model pair ∂μ.map joint := (lintegral_map hm hj).symm
    _ = ∫⁻ pair, model pair ∂ρ.prod ε := by rw [hlaw]
    _ = (∫⁻ fresh, charge fresh ∂ε) * ρ D := lintegral_source_rectangle ρ ε D hD charge hc
    _ = (∫⁻ fresh, charge fresh ∂ε) * μ cell := by rw [hcell, productGate_preimage_mass μ ρ ε joint hj hlaw D hD]

theorem productGate_cell_event (μ : Measure Sample) (ρ : Measure Gate) (ε : Measure Fresh)
    [IsProbabilityMeasure ε]
    (joint : Sample → Gate × Fresh) (hj : Measurable joint) (hlaw : μ.map joint = ρ.prod ε)
    (D : Set Gate) (hD : MeasurableSet D) (cell : Set Sample)
    (hcell : cell = joint ⁻¹' (D ×ˢ Set.univ))
    (event : Sample → Prop) (A : Set Fresh) (hA : MeasurableSet A)
    (hevent : ∀ᵐ sample ∂μ, sample ∈ cell → (event sample ↔ (joint sample).2 ∈ A)) :
    μ (cell ∩ {sample | event sample}) = ε A * μ cell := by
  have heq : cell ∩ {sample | event sample} =ᵐ[μ] joint ⁻¹' (D ×ˢ A) := by
    filter_upwards [hevent] with sample hs
    have hi : sample ∈ cell ↔ (joint sample).1 ∈ D := by rw [hcell]; simp
    apply propext
    change (sample ∈ cell ∧ event sample) ↔ ((joint sample).1 ∈ D ∧ (joint sample).2 ∈ A)
    rw [← hi]
    exact and_congr_right (fun h => hs h)
  calc
    _ = μ (joint ⁻¹' (D ×ˢ A)) := measure_congr heq
    _ = μ.map joint (D ×ˢ A) := (Measure.map_apply hj (hD.prod hA)).symm
    _ = ρ.prod ε (D ×ˢ A) := by rw [hlaw]
    _ = ε A * ρ D := by rw [Measure.prod_prod, mul_comm]
    _ = ε A * μ cell := by rw [hcell, productGate_preimage_mass μ ρ ε joint hj hlaw D hD]

end PDROC

