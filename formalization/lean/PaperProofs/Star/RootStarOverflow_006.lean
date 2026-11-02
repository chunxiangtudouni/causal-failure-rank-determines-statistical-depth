module

public import PaperProofs.Star.RootStarOverflow_005
public import PaperProofs.Star.PDROC_StarOverflowTail_002
public import PaperProofs.Star.RootStarQuota_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star
open PaperProofs.Star.Parameters PaperProofs.Statistics

universe u

noncomputable def overflowKernel (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ) (quota : ℕ)
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    Set ((P.input order).StageSample stage) :=
  match P.chosenTargetReal order kind r history stage with
  | none => ∅
  | some target => {point | point.1 = truth ∧
      (quota : ℕ∞) < realPosteriorStop ((P.input order).experiment stage) target point.2}

noncomputable def testingKernel (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    Set ((P.input order).StageSample stage) :=
  match P.chosenTargetReal order kind r history stage with
  | none => ∅
  | some _target => {point | point.1 = truth}

theorem measurable_realStop_stage (P : Parameters) (order : Order)
    (stage : (starInstance P.tools order).Stage) (target : ℝ) :
    Measurable (fun point : (P.input order).StageSample stage =>
      realPosteriorStop ((P.input order).experiment stage) target point.2) := by
  change Measurable (fun point : Bool × P.channel.experiment.Tape =>
    realPosteriorStop P.channel.experiment target point.2)
  have hp : Measurable (fun point : Bool × P.channel.experiment.Tape => ((), point.2)) :=
    measurable_const.prodMk measurable_snd
  have hm := (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel target)).measurable_stop.comp
    hp
  convert hm using 1
  funext point
  exact PStarLR.realPosteriorStop_eq_hitting P.channel target point.2

theorem measurable_overflowKernel (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ) (quota : ℕ)
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    MeasurableSet (overflowKernel P order kind r quota stage truth history) := by
  unfold overflowKernel
  split
  · exact MeasurableSet.empty
  · rename_i target _
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((Set.to_countable (Set.Ioi (quota : ℕ∞))).measurableSet.preimage
        (measurable_realStop_stage P order stage target))

theorem measurable_testingKernel (P : Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    MeasurableSet (testingKernel P order kind r stage truth history) := by
  unfold testingKernel
  split
  · exact MeasurableSet.empty
  · exact measurableSet_eq_fun measurable_fst measurable_const

theorem stage_overflow_bound (P : Parameters) (order : Order) (kind : PortKind)
    (delta : ℝ) (exponent : ℕ) (hd : 0 < delta) (hq : delta ≤ 1 / 2)
    (he : IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent)
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    (P.input order).stageLaw stage (overflowKernel P order kind (delta / 2) (P.commonQuota exponent) stage truth history) ≤
      ENNReal.ofReal (delta / (2 * (P.tools + 1 : ℕ))) *
        (P.input order).stageLaw stage (testingKernel P order kind (delta / 2) stage truth history) := by
  cases ht : P.chosenTargetReal order kind (delta / 2) history stage with
  | none => simp only [overflowKernel, testingKernel, ht, measure_empty, mul_zero, le_rfl]
  | some target =>
    have hb := RootStarQuota.chosenTarget_bounds P order kind (delta / 2)
      (by linarith) (by linarith) history stage target ht
    have hf : delta / 10 ≤ target := by
      simpa only [div_div, show (2 : ℝ) * 5 = 10 by norm_num] using hb.1
    have hp : 0 < target := lt_of_lt_of_le (by positivity : 0 < delta / 10) hf
    have htail := PDROC.StarOverflowTail.realPosteriorStop_commonQuota_tail P delta target exponent
      hd he hp hb.2 hf truth
    have ho : overflowKernel P order kind (delta / 2) (P.commonQuota exponent) stage truth history =
        {truth} ×ˢ {tape | (P.commonQuota exponent : ℕ∞) <
          realPosteriorStop ((P.input order).experiment stage) target tape} := by
      ext point
      simp only [overflowKernel, ht, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff]
    have hs : testingKernel P order kind (delta / 2) stage truth history =
        {truth} ×ˢ (Set.univ : Set ((P.input order).experiment stage).Tape) := by
      ext point
      simp only [testingKernel, ht, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
        Set.mem_univ, and_true]
    rw [ho, hs, (P.input order).stageLaw_truth_tape, (P.input order).stageLaw_truth_tape,
      measure_univ, mul_one]
    exact (mul_le_mul_of_nonneg_left htail zero_le).trans_eq (mul_comm _ _)

theorem overflow_event_preimage {Seed : Type u} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) (stage : (starInstance P.tools order).Stage)
    (truth : Bool) (gate : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) :
    P.entryOverflowEvent order kind r quota C accounting stage truth gate =
      (fun sample => (entryRecord (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) stage sample, sample.2 stage)) ⁻¹'
          historyKernelEvent gate (overflowKernel P order kind r quota stage truth) := by
  ext sample
  constructor
  · rintro ⟨history, target, hentry, hgate, ht, hx, hoverflow⟩
    refine ⟨history, hentry, hgate, ?_⟩
    simp only [overflowKernel, ht, Set.mem_ofPred_eq]
    exact ⟨hx, hoverflow⟩
  · rintro ⟨history, hentry, hgate, hkernel⟩
    change sample.2 stage ∈ overflowKernel P order kind r quota stage truth history at hkernel
    cases ht : P.chosenTargetReal order kind r history stage with
    | none => simp only [overflowKernel, ht, Set.mem_empty_iff_false] at hkernel
    | some target =>
      refine ⟨history, target, hentry, hgate, ht, ?_⟩
      change (sample.2 stage).1 = truth ∧
        (quota : ℕ∞) < realPosteriorStop ((P.input order).experiment stage) target (sample.2 stage).2
      simpa only [overflowKernel, ht, Set.mem_ofPred_eq] using hkernel

theorem testing_event_preimage {Seed : Type u} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) (stage : (starInstance P.tools order).Stage)
    (truth : Bool) (gate : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) :
    P.entryTestEvent order kind r C accounting stage truth gate =
      (fun sample => (entryRecord (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) stage sample, sample.2 stage)) ⁻¹'
          historyKernelEvent gate (testingKernel P order kind r stage truth) := by
  ext sample
  constructor
  · rintro ⟨history, target, hentry, hgate, ht, hx⟩
    exact ⟨history, hentry, hgate,
      by simpa only [testingKernel, ht, Set.mem_ofPred_eq, StatisticalInput.truthAt] using hx⟩
  · rintro ⟨history, hentry, hgate, hkernel⟩
    change sample.2 stage ∈ testingKernel P order kind r stage truth history at hkernel
    cases ht : P.chosenTargetReal order kind r history stage with
    | none => simp only [testingKernel, ht, Set.mem_empty_iff_false] at hkernel
    | some target =>
      exact ⟨history, target, hentry, hgate, ht,
        by simpa only [testingKernel, ht, Set.mem_ofPred_eq, StatisticalInput.truthAt] using hkernel⟩

theorem entry_overflow_le {Seed : Type u} [MeasurableSpace Seed]
    (P : Parameters) (order : Order) (kind : PortKind)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (delta : ℝ) (exponent : ℕ) (hd : 0 < delta) (hq : delta ≤ 1 / 2)
    (he : IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent)
    (hlegal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind (delta / 2) none (Seed := Seed)))
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    (stage : (starInstance P.tools order).Stage) (truth : Bool)
    (gate : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hgate : MeasurableSet gate) :
    (P.input order).seededWorldLaw nu
        (P.entryOverflowEvent order kind (delta / 2) (P.commonQuota exponent) C accounting stage truth gate) ≤
      ENNReal.ofReal (delta / (2 * (P.tools + 1 : ℕ))) *
        (P.input order).seededWorldLaw nu
          (P.entryTestEvent order kind (delta / 2) C accounting stage truth gate) := by
  let policy : Policy (P.input order) C .uncapped accounting Seed :=
    ⟨P.starReferenceRule order kind (delta / 2) none,
      P.measurable_starReferenceRule order kind (delta / 2) none, hlegal⟩
  let record := entryRecord (P.input order) C .uncapped accounting policy.rule stage
  let joint := fun sample : Seed × (P.input order).World => (record sample, sample.2 stage)
  let mu := ((P.input order).seededWorldLaw nu).map record
  have hr : Measurable record :=
    measurable_entryRecord (P.input order) C .uncapped accounting policy.rule policy.measurable_rule stage
  have hj : Measurable joint := hr.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hmap : ((P.input order).seededWorldLaw nu).map joint = mu.prod ((P.input order).stageLaw stage) :=
    entryRecord_jointLaw (P.input order) C .uncapped accounting policy nu stage
  let over := overflowKernel P order kind (delta / 2) (P.commonQuota exponent) stage truth
  let base := testingKernel P order kind (delta / 2) stage truth
  have hmO : MeasurableSet (historyKernelEvent gate over) :=
    measurableSet_historyKernelEvent gate hgate over
      (measurable_overflowKernel P order kind (delta / 2) (P.commonQuota exponent) stage truth)
  have hmB : MeasurableSet (historyKernelEvent gate base) :=
    measurableSet_historyKernelEvent gate hgate base
      (measurable_testingKernel P order kind (delta / 2) stage truth)
  calc
    _ = ((P.input order).seededWorldLaw nu).map joint (historyKernelEvent gate over) := by
      rw [Measure.map_apply hj hmO]
      exact congrArg ((P.input order).seededWorldLaw nu)
        (overflow_event_preimage P order kind (delta / 2) (P.commonQuota exponent) C accounting stage truth gate)
    _ = mu.prod ((P.input order).stageLaw stage) (historyKernelEvent gate over) := by rw [hmap]
    _ ≤ _ := historyKernel_product_bound mu ((P.input order).stageLaw stage) gate hgate over base
      (measurable_overflowKernel P order kind (delta / 2) (P.commonQuota exponent) stage truth)
      (measurable_testingKernel P order kind (delta / 2) stage truth)
      _ (stage_overflow_bound P order kind delta exponent hd hq he stage truth)
    _ = _ := by
      rw [← hmap, Measure.map_apply hj hmB]
      exact congrArg (fun value : ℝ≥0∞ => ENNReal.ofReal (delta / (2 * (P.tools + 1 : ℕ))) * value)
        (congrArg ((P.input order).seededWorldLaw nu)
          (testing_event_preimage P order kind (delta / 2) C accounting stage truth gate)).symm

end RootStarOverflow
