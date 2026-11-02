module

public import PaperProofs.Paid.PDLower_Cost_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem gated_perspective {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hph : ∀ i a, p i a ≤ 1 / 2)
    (hpm : ∀ i, Measurable (fun a => ENNReal.ofReal (p i a)))
    (m b : ℝ) (hm : 0 < m) (hb : 0 < b) (hbh : b / m ≤ 1 / 2)
    (hmass : ENNReal.ofReal m ≤ ∑ i, μ (E i))
    (hpost : (∑ i, ∫⁻ a, (E i).indicator (fun a => ENNReal.ofReal (p i a)) a ∂μ) ≤ ENNReal.ofReal b) :
    ENNReal.ofReal m * phi (b / m) ≤
      ∑ i, ∫⁻ a, (E i).indicator (fun a => phi (p i a)) a ∂μ := by
  classical
  let z := b / m
  let k := -phiDerivative z
  let A := phiReal z + k * z
  have hz : 0 < z := div_pos hb hm
  have hk : 0 ≤ k := neg_nonneg.mpr (phiDerivative_nonpos hz hbh)
  have hφ : 0 ≤ phiReal z := phiReal_nonneg hz hbh
  have hA : 0 ≤ A := add_nonneg hφ (mul_nonneg hk hz.le)
  have hlocal (i : ι) : ENNReal.ofReal A * μ (E i) ≤
      (∫⁻ a, (E i).indicator (fun a => phi (p i a)) a ∂μ) +
        ENNReal.ofReal k * ∫⁻ a, (E i).indicator (fun a => ENNReal.ofReal (p i a)) a ∂μ := by
    have hkg : Measurable (fun a => ENNReal.ofReal k * (E i).indicator (fun a => ENNReal.ofReal (p i a)) a) :=
      measurable_const.mul ((hpm i).indicator (hE i))
    rw [← lintegral_indicator_const (hE i), ← lintegral_const_mul _ ((hpm i).indicator (hE i)),
      ← lintegral_add_right _ hkg]
    apply lintegral_mono
    intro a
    by_cases ha : a ∈ E i
    · simpa only [Set.indicator_of_mem ha] using phi_support hz hbh (hp i a) (hph i a)
    · simp only [Set.indicator_of_notMem ha, mul_zero, add_zero, le_refl]
  have hsum : ENNReal.ofReal A * (∑ i, μ (E i)) ≤
      (∑ i, ∫⁻ a, (E i).indicator (fun a => phi (p i a)) a ∂μ) +
        ENNReal.ofReal k * (∑ i, ∫⁻ a, (E i).indicator (fun a => ENNReal.ofReal (p i a)) a ∂μ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => hlocal i)
  have hcancel : ENNReal.ofReal m * phi z + ENNReal.ofReal k * ENNReal.ofReal b ≤
      (∑ i, ∫⁻ a, (E i).indicator (fun a => phi (p i a)) a ∂μ) +
        ENNReal.ofReal k * ENNReal.ofReal b := by
    calc
      _ = ENNReal.ofReal (m * phiReal z + k * b) := by
        rw [phi_of_pos hz, ← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_mul hk,
          ← ENNReal.ofReal_add (mul_nonneg hm.le hφ) (mul_nonneg hk hb.le)]
      _ = ENNReal.ofReal A * ENNReal.ofReal m := by
        rw [← ENNReal.ofReal_mul hA]
        congr 1
        dsimp [A, z]
        field_simp
      _ ≤ ENNReal.ofReal A * (∑ i, μ (E i)) := mul_le_mul' le_rfl hmass
      _ ≤ _ := hsum.trans (add_le_add le_rfl (mul_le_mul' le_rfl hpost))
  exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hcancel

end PDLower
