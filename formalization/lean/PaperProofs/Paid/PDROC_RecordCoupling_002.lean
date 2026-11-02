module
public import PaperProofs.Paid.PDROC_RecordCoupling_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC
universe u

theorem measurable_recordVirtualTruth_family (P : PaperProofs.Paid.Parameters) (actualTruth : Bool) :
    Measurable (fun pair : AuxiliaryRecord × (Bool × P.binarySymmetric.experiment.Tape) =>
      recordVirtualTruth P pair.1 actualTruth pair.2) :=
  measurable_from_prod_countable_right (fun record => measurable_recordVirtualTruth P record actualTruth)

section
variable {Source : Type u} [MeasurableSpace Source]

/-- The original source coordinate is retained verbatim; it can hold the
old private seed together with the complete virtual entry history. -/
noncomputable def coupledRecordTruth (P : PaperProofs.Paid.Parameters) (recordOf : Source → AuxiliaryRecord)
    (actualTruth : Bool) (pair : Source × (Bool × P.binarySymmetric.experiment.Tape)) : Source × Bool :=
  (pair.1, recordVirtualTruth P (recordOf pair.1) actualTruth pair.2)

theorem measurable_coupledRecordTruth (P : PaperProofs.Paid.Parameters)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf) (actualTruth : Bool) :
    Measurable (coupledRecordTruth P recordOf actualTruth) := by
  unfold coupledRecordTruth
  have hpair : Measurable (fun pair : Source × (Bool × P.binarySymmetric.experiment.Tape) =>
      (recordOf pair.1, pair.2)) := (hr.comp measurable_fst).prodMk measurable_snd
  have hm := (measurable_recordVirtualTruth_family P actualTruth).comp hpair
  change Measurable (fun pair : Source × (Bool × P.binarySymmetric.experiment.Tape) =>
    recordVirtualTruth P (recordOf pair.1) actualTruth pair.2) at hm
  have hfst : Measurable (Prod.fst : Source × (Bool × P.binarySymmetric.experiment.Tape) → Source) := measurable_fst
  exact hfst.prodMk hm

/-- The target is independently the source law weighted by the actual
finite-word posterior masses, not a law defined through the simulator. -/
noncomputable def posteriorRecordLaw (P : PaperProofs.Paid.Parameters)
    (recordOf : Source → AuxiliaryRecord) (ρ : Measure Source) : Measure (Source × Bool) :=
  (ρ.withDensity (fun source => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass false
    ⟨(recordOf source).observations.length, fun k => (recordOf source).observations[k.val]⟩))).map
      (fun source => (source, false)) +
  (ρ.withDensity (fun source => ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass true
    ⟨(recordOf source).observations.length, fun k => (recordOf source).observations[k.val]⟩))).map
      (fun source => (source, true))

theorem posteriorRecordLaw_rectangle_singleton (P : PaperProofs.Paid.Parameters)
    (recordOf : Source → AuxiliaryRecord) (ρ : Measure Source) (B : Set Source)
    (hB : MeasurableSet B) (truth : Bool) :
    posteriorRecordLaw P recordOf ρ (B ×ˢ {truth}) =
      ∫⁻ source in B, ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass truth
        ⟨(recordOf source).observations.length, fun k => (recordOf source).observations[k.val]⟩) ∂ρ := by
  have hf : Measurable (fun source : Source => (source, false)) := measurable_id.prodMk measurable_const
  have ht : Measurable (fun source : Source => (source, true)) := measurable_id.prodMk measurable_const
  have hpre (bit : Bool) : (fun source : Source => (source, bit)) ⁻¹' (B ×ˢ {truth}) =
      if bit = truth then B else ∅ := by
    ext source
    by_cases hb : bit = truth <;> simp [hb]
  unfold posteriorRecordLaw
  rw [Measure.add_apply, Measure.map_apply hf (hB.prod (measurableSet_singleton truth)),
    Measure.map_apply ht (hB.prod (measurableSet_singleton truth)), hpre, hpre]
  cases truth <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, measure_empty,
    zero_add, add_zero, withDensity_apply _ hB]

/-- Exact source-coordinate/posterior coupling on every measurable source
event, conditionally for either real truth. The fresh endpoint experiment
is independent of the source coordinate under the genuine product law. -/
theorem coupledRecordTruth_rectangle_singleton (P : PaperProofs.Paid.Parameters)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf)
    (ρ : Measure Source) [IsProbabilityMeasure ρ] (B : Set Source) (hB : MeasurableSet B)
    (actualTruth virtualTruth : Bool) :
    ((ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)).map
      (coupledRecordTruth P recordOf actualTruth)) (B ×ˢ {virtualTruth}) =
      ∫⁻ source in B, ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass virtualTruth
        ⟨(recordOf source).observations.length, fun k => (recordOf source).observations[k.val]⟩) ∂ρ := by
  classical
  have hm := measurable_coupledRecordTruth P recordOf hr actualTruth
  have hset := hm (hB.prod (measurableSet_singleton virtualTruth))
  rw [Measure.map_apply hm (hB.prod (measurableSet_singleton virtualTruth)), Measure.prod_apply hset,
    ← lintegral_indicator hB]
  apply lintegral_congr
  intro source
  have hpre : Prod.mk source ⁻¹' ((coupledRecordTruth P recordOf actualTruth) ⁻¹' (B ×ˢ {virtualTruth})) =
      if source ∈ B then {sample | recordVirtualTruth P (recordOf source) actualTruth sample = virtualTruth}
      else ∅ := by
    ext sample
    by_cases hs : source ∈ B <;> simp [coupledRecordTruth, hs]
  rw [hpre]
  by_cases hs : source ∈ B
  · simp only [hs, ↓reduceIte, Set.indicator_of_mem hs]
    exact recordVirtualTruth_singleton_probability P (recordOf source) actualTruth virtualTruth
  · simp only [hs, ↓reduceIte, measure_empty, Set.indicator_of_notMem hs]

/-- The full original-source/virtual-truth joint law equals the independently
defined posterior law. Arbitrary source universes and measurable source
record selection are preserved. No future truth is part of the private seed. -/
theorem coupledRecordTruth_jointLaw (P : PaperProofs.Paid.Parameters)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf)
    (ρ : Measure Source) [IsProbabilityMeasure ρ] (actualTruth : Bool) :
    (ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth)).map
      (coupledRecordTruth P recordOf actualTruth) = posteriorRecordLaw P recordOf ρ := by
  apply Measure.ext_prod
  intro B facts hB _hfacts
  have hset : B ×ˢ facts = ⋃ truth : facts, B ×ˢ {truth.val} := by
    ext pair
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hpair, hfact⟩
      exact ⟨⟨pair.2, hfact⟩, hpair, rfl⟩
    · rintro ⟨truth, hpair, htruth⟩
      exact ⟨hpair, htruth ▸ truth.property⟩
  have hdisj : Pairwise (fun truth truth' : facts => Disjoint (B ×ˢ {truth.val}) (B ×ˢ {truth'.val})) := by
    intro truth truth' hne
    apply Set.disjoint_left.mpr
    intro pair hp hp'
    exact hne (Subtype.ext (hp.2.symm.trans hp'.2))
  have hmeas (truth : facts) : MeasurableSet (B ×ˢ {truth.val}) := hB.prod (measurableSet_singleton truth.val)
  rw [hset, measure_iUnion hdisj hmeas, measure_iUnion hdisj hmeas]
  apply tsum_congr
  intro truth
  rw [coupledRecordTruth_rectangle_singleton P recordOf hr ρ B hB actualTruth truth.val,
    posteriorRecordLaw_rectangle_singleton P recordOf ρ B hB truth.val]

end
end PDROC





