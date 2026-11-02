module

public import PaperProofs.Star.RootStarOverflow_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootStarOverflow

universe u

def historyKernelEvent {Seed : Type u} {History Sample : Type*}
    (gate : Set (Seed × History)) (kernel : History → Set Sample) :
    Set ((Seed × Option History) × Sample) :=
  {point | ∃ history, point.1.2 = some history ∧ (point.1.1, history) ∈ gate ∧ point.2 ∈ kernel history}

theorem measurableSet_historyKernelEvent {Seed : Type u} {History Sample : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History] [MeasurableSpace Sample]
    [MeasurableSpace (Option History)] [MeasurableSingletonClass (Option History)]
    [Countable History] [MeasurableSingletonClass History]
    (gate : Set (Seed × History)) (hgate : MeasurableSet gate)
    (kernel : History → Set Sample) (hkernel : ∀ history, MeasurableSet (kernel history)) :
    MeasurableSet (historyKernelEvent gate kernel) := by
  have heq : historyKernelEvent gate kernel =
      ⋃ history, {record : Seed × Option History |
        record.2 = some history ∧ (record.1, history) ∈ gate} ×ˢ kernel history := by
    ext point
    simp only [historyKernelEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod]
    exact exists_congr (fun _ => and_assoc.symm)
  rw [heq]
  apply MeasurableSet.iUnion
  intro history
  apply MeasurableSet.prod _ (hkernel history)
  exact (measurable_snd (measurableSet_singleton (some history))).inter
    (hgate.preimage (measurable_fst.prodMk measurable_const))

theorem historyKernel_section_none {Seed : Type u} {History Sample : Type*}
    (gate : Set (Seed × History)) (kernel : History → Set Sample) (record : Seed × Option History)
    (h : record.2 = none) :
    Prod.mk record ⁻¹' historyKernelEvent gate kernel = ∅ := by
  ext sample
  simp [historyKernelEvent, h]

theorem historyKernel_section_some {Seed : Type u} {History Sample : Type*}
    (gate : Set (Seed × History)) (kernel : History → Set Sample) (record : Seed × Option History)
    (history : History) (h : record.2 = some history) :
    Prod.mk record ⁻¹' historyKernelEvent gate kernel =
      {sample | (record.1, history) ∈ gate ∧ sample ∈ kernel history} := by
  ext sample
  simp [historyKernelEvent, h]

theorem historyKernel_product_bound {Seed : Type u} {History Sample : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History] [MeasurableSpace Sample]
    [MeasurableSpace (Option History)] [MeasurableSingletonClass (Option History)]
    [Countable History] [MeasurableSingletonClass History]
    (mu : Measure (Seed × Option History)) (rho : Measure Sample) [SFinite rho]
    (gate : Set (Seed × History)) (hgate : MeasurableSet gate)
    (overflow base : History → Set Sample)
    (hoverflow : ∀ history, MeasurableSet (overflow history))
    (hbase : ∀ history, MeasurableSet (base history)) (cap : ℝ≥0∞)
    (hbound : ∀ history, rho (overflow history) ≤ cap * rho (base history)) :
    mu.prod rho (historyKernelEvent gate overflow) ≤ cap * mu.prod rho (historyKernelEvent gate base) := by
  have hmO := measurableSet_historyKernelEvent gate hgate overflow hoverflow
  have hmB := measurableSet_historyKernelEvent gate hgate base hbase
  rw [Measure.prod_apply hmO, Measure.prod_apply hmB,
    ← lintegral_const_mul cap (measurable_measure_prodMk_left hmB)]
  apply lintegral_mono
  intro record
  change rho (Prod.mk record ⁻¹' historyKernelEvent gate overflow) ≤
    cap * rho (Prod.mk record ⁻¹' historyKernelEvent gate base)
  cases hh : record.2 with
  | none => simp only [historyKernel_section_none gate overflow record hh,
      historyKernel_section_none gate base record hh, measure_empty, mul_zero, le_rfl]
  | some history =>
    rw [historyKernel_section_some gate overflow record history hh,
      historyKernel_section_some gate base record history hh]
    by_cases hg : (record.1, history) ∈ gate
    · simp only [hg, true_and]
      exact hbound history
    · simp only [hg, false_and, Set.ofPred_false, measure_empty, mul_zero, le_rfl]

end RootStarOverflow
