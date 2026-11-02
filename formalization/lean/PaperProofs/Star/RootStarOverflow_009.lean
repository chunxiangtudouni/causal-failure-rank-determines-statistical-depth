module

public import PaperProofs.Star.RootStarOverflow_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

universe u

theorem measurable_entryTestEvent {Seed : Type u} [MeasurableSpace Seed]
    (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (gate : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hgate : MeasurableSet gate) :
    MeasurableSet (P.entryTestEvent order kind r C accounting stage truth gate) := by
  rw [testing_event_preimage]
  apply (measurableSet_historyKernelEvent gate hgate _
    (measurable_testingKernel P order kind r stage truth)).preimage
  exact (measurable_entryRecord (P.input order) C .uncapped accounting _
    (P.measurable_starReferenceRule order kind r none) stage).prodMk
      ((measurable_pi_apply stage).comp measurable_snd)

theorem entry_truth_probability_sum (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (stage : (starInstance P.tools order).Stage) :
    (∑ truth : Bool, (P.input order).seededWorldLaw (Measure.dirac ())
      (P.entryTestEvent order kind r C accounting stage truth Set.univ)) ≤ 1 := by
  let event := fun truth : Bool => P.entryTestEvent order kind r C accounting stage truth (Set.univ : Set (Unit × _))
  have hd : Disjoint (event true) (event false) := by
    apply Set.disjoint_left.mpr
    intro sample ht hf
    obtain ⟨_, _, _, _, _, hx⟩ := ht
    obtain ⟨_, _, _, _, _, hy⟩ := hf
    have h : true = false := hx.symm.trans hy
    cases h
  have hm : MeasurableSet (event false) := measurable_entryTestEvent P order kind r C accounting stage false _ MeasurableSet.univ
  have hsum : (P.input order).seededWorldLaw (Measure.dirac ()) (event true) +
      (P.input order).seededWorldLaw (Measure.dirac ()) (event false) ≤ 1 := by
    rw [← measure_union hd hm]
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  simpa only [Fintype.sum_bool] using hsum

theorem anyStarOverflow_le (P : Parameters) (order : Order) (kind : PortKind)
    (C : Contract (starInstance P.tools order)) (hC : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (delta : ℝ) (exponent : ℕ)
    (hd : 0 < delta) (hq : delta ≤ 1 / 2)
    (he : PaperProofs.Statistics.IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent) :
    (P.input order).seededWorldLaw (Measure.dirac ())
      (P.anyStarOverflow order kind (delta / 2) (P.commonQuota exponent) C accounting) ≤
        ENNReal.ofReal (delta / 2) := by
  let law := (P.input order).seededWorldLaw (Measure.dirac ())
  let cap := ENNReal.ofReal (delta / (2 * (P.tools + 1 : ℕ)))
  have hcard : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools + 1 := by
    rw [Finset.card_univ]
    rw [Fintype.card_fin]
    simp only [starInstance, List.length_ofFn]
  have hstage (stage : (starInstance P.tools order).Stage) :
      law (⋃ truth : Bool, P.entryOverflowEvent order kind (delta / 2) (P.commonQuota exponent)
        C accounting stage truth (Set.univ : Set (Unit × _))) ≤ cap := by
    calc
      _ ≤ ∑ truth : Bool, law (P.entryOverflowEvent order kind (delta / 2) (P.commonQuota exponent)
          C accounting stage truth (Set.univ : Set (Unit × _))) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ truth : Bool, cap * law (P.entryTestEvent order kind (delta / 2) C accounting stage truth Set.univ) := by
        apply Finset.sum_le_sum
        intro truth _
        exact conditionalOverflow P order kind C hC accounting delta exponent hd hq he
          Unit inferInstance (Measure.dirac ()) inferInstance stage truth Set.univ MeasurableSet.univ
      _ = cap * ∑ truth : Bool, law (P.entryTestEvent order kind (delta / 2) C accounting stage truth Set.univ) := by
        rw [Finset.mul_sum]
      _ ≤ cap * 1 := mul_le_mul_of_nonneg_left (entry_truth_probability_sum P order kind (delta / 2) C accounting stage) zero_le
      _ = cap := mul_one _
  calc
    _ ≤ ∑ stage : (starInstance P.tools order).Stage,
        law (⋃ truth : Bool, P.entryOverflowEvent order kind (delta / 2) (P.commonQuota exponent)
          C accounting stage truth (Set.univ : Set (Unit × _))) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _stage : (starInstance P.tools order).Stage, cap := Finset.sum_le_sum (fun stage _ => hstage stage)
    _ = (P.tools + 1 : ℕ) * cap := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_add, Nat.cast_one]
    _ = _ := by
      dsimp only [cap]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (P.tools + 1 : ℕ))]
      congr 1
      have hn : (P.tools + 1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp

end RootStarOverflow
