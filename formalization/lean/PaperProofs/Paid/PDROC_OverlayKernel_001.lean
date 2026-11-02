module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Statistics.PDROC_ExactAttainment_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid PaperProofs.Statistics.BinarySymmetric
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u

variable {X : Type u} [MeasurableSpace X]

/-- The independent extra mark creates only false positives: actual errors
remain included on every sample, not merely almost surely. -/
def overlayKernelVirtualEvent (A : Set X) : Set (X × Bool) :=
  (A ×ˢ Set.univ) ∪ (Aᶜ ×ˢ {true})

omit [MeasurableSpace X] in
theorem overlayKernel_actual_subset (A : Set X) :
    A ×ˢ (Set.univ : Set Bool) ⊆ overlayKernelVirtualEvent A := Set.subset_union_left

theorem measurableSet_overlayKernelVirtualEvent (A : Set X) (hA : MeasurableSet A) :
    MeasurableSet (overlayKernelVirtualEvent A) :=
  (hA.prod MeasurableSet.univ).union (hA.compl.prod (measurableSet_singleton true))

theorem overlayKernel_falsePositive_cell
    (μ : Measure X) (q : Set.Icc (0 : ℝ) 1) (A B : Set X) :
    (μ.prod (rocCoinLaw q))
        (((B ∩ Aᶜ) ×ˢ Set.univ) ∩ overlayKernelVirtualEvent A) =
      ENNReal.ofReal q.val * (μ.prod (rocCoinLaw q)) ((B ∩ Aᶜ) ×ˢ Set.univ) := by
  have hset : (((B ∩ Aᶜ) ×ˢ Set.univ) ∩ overlayKernelVirtualEvent A) =
      (B ∩ Aᶜ) ×ˢ {true} := by
    ext ⟨x, b⟩
    by_cases hx : x ∈ A <;> simp [overlayKernelVirtualEvent, hx]
  rw [hset, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one]
  have hcoin : rocCoinLaw q {true} = ENNReal.ofReal q.val := by
    simp [rocCoinLaw]
  rw [hcoin, mul_comm]

/-- Generic fixed-record error coupling. The only input probabilities are
the actual MAP error p and the desired original decision error e. -/
theorem overlayKernel_virtual_probability
    (μ : Measure X) [IsProbabilityMeasure μ] (A : Set X) (hA : MeasurableSet A)
    (p e : ℝ) (hp : 0 ≤ p) (hpone : p < 1) (hpe : p ≤ e) (he : e ≤ 1)
    (herr : μ A = ENNReal.ofReal p) :
    let q : Set.Icc (0 : ℝ) 1 :=
      ⟨PaperProofs.Paid.Parameters.falsePositiveProbability e p,
        PaperProofs.Paid.Parameters.falsePositiveProbability_mem_Icc e p hp hpone hpe he⟩
    (μ.prod (rocCoinLaw q)) (overlayKernelVirtualEvent A) = ENNReal.ofReal e := by
  dsimp only
  let q : Set.Icc (0 : ℝ) 1 :=
    ⟨PaperProofs.Paid.Parameters.falsePositiveProbability e p,
      PaperProofs.Paid.Parameters.falsePositiveProbability_mem_Icc e p hp hpone hpe he⟩
  have hd : Disjoint (A ×ˢ (Set.univ : Set Bool)) (Aᶜ ×ˢ {true}) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.1 hx.1
  have hcoin : rocCoinLaw q {true} = ENNReal.ofReal q.val := by simp [rocCoinLaw]
  have hcomp : μ Aᶜ = ENNReal.ofReal (1 - p) := by
    rw [measure_compl hA (measure_ne_top _ _), measure_univ, herr]
    rw [ENNReal.ofReal_sub 1 hp]
    norm_num
  change (μ.prod (rocCoinLaw q)) (overlayKernelVirtualEvent A) = _
  rw [overlayKernelVirtualEvent, measure_union hd
    (hA.compl.prod (measurableSet_singleton true)), Measure.prod_prod, Measure.prod_prod,
    measure_univ, mul_one, herr, hcomp, hcoin,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hpone.le),
    ← ENNReal.ofReal_add hp (mul_nonneg (sub_nonneg.mpr hpone.le) q.property.1)]
  congr 1
  exact PaperProofs.Paid.Parameters.falsePositiveProbability_mix e p hpone

end PDROC
