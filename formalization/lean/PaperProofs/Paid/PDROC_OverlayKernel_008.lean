module

public import PaperProofs.Paid.PDROC_OverlayKernel_003
public import PaperProofs.Paid.PDROC_OverlayCoins_003
public import PaperProofs.Paid.PDROC_RecordCoupling_002
public import PaperProofs.Paid.PDROC_SimulatorLaw_005
public import PaperProofs.Paid.PDROC_SimulatorLaw_007
public import PaperProofs.Paid.PDROC_OverlayTermination_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

/-! A single coherent stage-kernel batch. It consolidates the unexported
004--007 source sketches, retaining those originals as historical drafts.
No frozen source is changed and no original target is weakened. -/

namespace PDROC

universe u

def overlayRowExperimentSample (P : Parameters) (record : AuxiliaryRecord)
    (sample : OverlayStageCoins × P.experiment.Tape) :
    (((Bool × Bool) × P.experiment.Tape) × Bool) :=
  ((sample.1.1 record, sample.2), sample.1.2 record)

theorem measurable_overlayRowExperimentSample (P : Parameters) (record : AuxiliaryRecord) :
    Measurable (overlayRowExperimentSample P record) :=
  (((measurable_pi_apply record).comp (measurable_fst.comp measurable_fst)).prodMk
    measurable_snd).prodMk
      ((measurable_pi_apply record).comp (measurable_snd.comp measurable_fst))

noncomputable def overlayRowConditionalLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (truth : Bool) : Measure (OverlayStageCoins × P.experiment.Tape) :=
  (overlayPaidStageCoinsLaw P fee hfee).prod (P.experiment.tapeLaw truth)

instance overlayRowConditionalLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (truth : Bool) : IsProbabilityMeasure (overlayRowConditionalLaw P fee hfee truth) := by
  unfold overlayRowConditionalLaw
  infer_instance

/-- Looking up a fixed record in the independent private row and retaining
the actual tape gives exactly the already verified local experiment. -/
theorem overlayRowConditionalLaw_experiment (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    (overlayRowConditionalLaw P fee hfee truth).map (overlayRowExperimentSample P record) =
      overlayLocalExperimentLaw P fee hfee record truth := by
  let mix := overlayPaidMixtureLaw P fee hfee record
  let mark := overlayPaidMarkLaw P fee hfee record
  let tape := P.experiment.tapeLaw truth
  let lookup := fun coins : OverlayStageCoins => overlayStageCoinLookup coins record
  let rearrange := fun sample : ((Bool × Bool) × Bool) × P.experiment.Tape =>
    ((sample.1.1, sample.2), sample.1.2)
  have hl : Measurable lookup := measurable_overlayStageCoinLookup record
  have hp : Measurable (Prod.map lookup (id : P.experiment.Tape → _)) := hl.prodMap measurable_id
  have hr : Measurable rearrange := by fun_prop
  have hlookup : ((overlayPaidStageCoinsLaw P fee hfee).prod tape).map (Prod.map lookup id) =
      (mix.prod mark).prod tape := by
    rw [← Measure.map_prod_map _ _ hl measurable_id, Measure.map_id,
      overlayPaidStageCoinsLaw_lookup]
  have h1 := measurePreserving_prodAssoc mix mark tape
  have h2 := (MeasurePreserving.id mix).prod
    (Measure.measurePreserving_swap (μ := mark) (ν := tape))
  have h3 := (measurePreserving_prodAssoc mix tape mark).symm MeasurableEquiv.prodAssoc
  have hperm : ((mix.prod mark).prod tape).map rearrange = (mix.prod tape).prod mark :=
    ((h3.comp h2).comp h1).map_eq
  change (((overlayPaidStageCoinsLaw P fee hfee).prod tape).map
    (rearrange ∘ Prod.map lookup id)) = _
  rw [← Measure.map_map hr hp, hlookup, hperm]
  rfl

noncomputable def overlayRowVirtualTruth (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) (sample : OverlayStageCoins × P.experiment.Tape) : Bool :=
  overlayLocalVirtualTruth P fee hfee record truth (overlayRowExperimentSample P record sample)

theorem measurable_overlayRowVirtualTruth (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    Measurable (overlayRowVirtualTruth P fee hfee record truth) :=
  (measurable_overlayLocalVirtualTruth P fee hfee record truth).comp
    (measurable_overlayRowExperimentSample P record)

theorem overlayRowVirtualTruth_singleton_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth virtualTruth : Bool) :
    overlayRowConditionalLaw P fee hfee truth
      {sample | overlayRowVirtualTruth P fee hfee record truth sample = virtualTruth} =
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass virtualTruth
        (auxiliaryRecordWord P record)) := by
  let μ := overlayRowConditionalLaw P fee hfee truth
  let f := overlayRowExperimentSample P record
  let A : Set (((Bool × Bool) × P.experiment.Tape) × Bool) :=
    {sample | overlayLocalVirtualTruth P fee hfee record truth sample = virtualTruth}
  have hA : MeasurableSet A := (measurable_overlayLocalVirtualTruth P fee hfee record truth)
    (measurableSet_singleton virtualTruth)
  have happ : (μ.map f) A = μ (f ⁻¹' A) :=
    Measure.map_apply (measurable_overlayRowExperimentSample P record) hA
  change μ (f ⁻¹' A) = _
  calc
    _ = (μ.map f) A := happ.symm
    _ = overlayLocalExperimentLaw P fee hfee record truth A :=
      congrArg (fun ρ => ρ A) (overlayRowConditionalLaw_experiment P fee hfee record truth)
    _ = _ := overlayLocal_virtualTruth_singleton_probability P fee hfee record truth virtualTruth

theorem measurable_overlayRowVirtualTruth_family (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (truth : Bool) :
    Measurable (fun pair : AuxiliaryRecord × (OverlayStageCoins × P.experiment.Tape) =>
      overlayRowVirtualTruth P fee hfee pair.1 truth pair.2) :=
  measurable_from_prod_countable_right (fun record => measurable_overlayRowVirtualTruth P fee hfee record truth)

variable {Source : Type u} [MeasurableSpace Source]

noncomputable def overlayCoupledRecordTruth (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (recordOf : Source → AuxiliaryRecord) (truth : Bool)
    (sample : Source × (OverlayStageCoins × P.experiment.Tape)) : Source × Bool :=
  (sample.1, overlayRowVirtualTruth P fee hfee (recordOf sample.1) truth sample.2)

set_option maxHeartbeats 800000 in
theorem measurable_overlayCoupledRecordTruth (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf) (truth : Bool) :
    Measurable (overlayCoupledRecordTruth P fee hfee recordOf truth) := by
  unfold overlayCoupledRecordTruth
  have hpair : Measurable (fun pair : Source × (OverlayStageCoins × P.experiment.Tape) =>
      (recordOf pair.1, pair.2)) := (hr.comp measurable_fst).prodMk measurable_snd
  have hm := (measurable_overlayRowVirtualTruth_family P fee hfee truth).comp hpair
  change Measurable (fun pair : Source × (OverlayStageCoins × P.experiment.Tape) =>
    overlayRowVirtualTruth P fee hfee (recordOf pair.1) truth pair.2) at hm
  have hfst : Measurable (Prod.fst : Source × (OverlayStageCoins × P.experiment.Tape) → Source) := measurable_fst
  exact hfst.prodMk hm

/-- All measurable gates on the complete old-seed/virtual-entry coordinate
are retained. Current selected mixture and FP marks remain integrated. -/
theorem overlayCoupledRecordTruth_rectangle_singleton (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf)
    (ρ : Measure Source) (B : Set Source) (hB : MeasurableSet B) (truth virtualTruth : Bool) :
    ((ρ.prod (overlayRowConditionalLaw P fee hfee truth)).map
      (overlayCoupledRecordTruth P fee hfee recordOf truth)) (B ×ˢ {virtualTruth}) =
      ∫⁻ source in B, ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass virtualTruth
        (auxiliaryRecordWord P (recordOf source))) ∂ρ := by
  classical
  have hm := measurable_overlayCoupledRecordTruth P fee hfee recordOf hr truth
  have hs := hm (hB.prod (measurableSet_singleton virtualTruth))
  rw [Measure.map_apply hm (hB.prod (measurableSet_singleton virtualTruth)),
    Measure.prod_apply hs, ← lintegral_indicator hB]
  apply lintegral_congr
  intro source
  have hpre : Prod.mk source ⁻¹' ((overlayCoupledRecordTruth P fee hfee recordOf truth) ⁻¹'
      (B ×ˢ {virtualTruth})) =
      if source ∈ B then {sample | overlayRowVirtualTruth P fee hfee (recordOf source) truth sample = virtualTruth}
      else ∅ := by
    ext sample
    by_cases hb : source ∈ B <;> simp [overlayCoupledRecordTruth, hb]
  rw [hpre]
  by_cases hb : source ∈ B
  · simp only [hb, ↓reduceIte, Set.indicator_of_mem hb]
    exact overlayRowVirtualTruth_singleton_probability P fee hfee (recordOf source) truth virtualTruth
  · simp only [hb, ↓reduceIte, measure_empty, Set.indicator_of_notMem hb]

/-- Full original-source/posterior-truth joint law, for either actual truth.
Finiteness here is only the gate measure's finiteness; original simulations
use probability gates and retain arbitrary private-seed universes. -/
theorem overlayCoupledRecordTruth_jointLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (recordOf : Source → AuxiliaryRecord) (hr : Measurable recordOf)
    (ρ : Measure Source) [IsFiniteMeasure ρ] (truth : Bool) :
    (ρ.prod (overlayRowConditionalLaw P fee hfee truth)).map
      (overlayCoupledRecordTruth P fee hfee recordOf truth) = posteriorRecordLaw P recordOf ρ := by
  apply Measure.ext_prod
  intro B facts hB _hfacts
  have hset : B ×ˢ facts = ⋃ bit : facts, B ×ˢ {bit.val} := by
    ext pair
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hf⟩
      exact ⟨⟨pair.2, hf⟩, hb, rfl⟩
    · rintro ⟨bit, hb, he⟩
      exact ⟨hb, he ▸ bit.property⟩
  have hd : Pairwise (fun bit bit' : facts => Disjoint (B ×ˢ {bit.val}) (B ×ˢ {bit'.val})) := by
    intro bit bit' hne
    apply Set.disjoint_left.mpr
    intro pair hp hp'
    exact hne (Subtype.ext (hp.2.symm.trans hp'.2))
  have hm (bit : facts) : MeasurableSet (B ×ˢ {bit.val}) := hB.prod (measurableSet_singleton bit.val)
  rw [hset, measure_iUnion hd hm, measure_iUnion hd hm]
  apply tsum_congr
  intro bit
  rw [overlayCoupledRecordTruth_rectangle_singleton P fee hfee recordOf hr ρ B hB truth bit.val,
    posteriorRecordLaw_rectangle_singleton P recordOf ρ B hB bit.val]
  rfl

end PDROC

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- For either real truth, the actual record-aware MAP/FP experiment
reproduces the original free source's FULL seed/entry/draw/reported-truth
law, not only the scalar error probability. -/
theorem overlayDraw_reportCouplingLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod
      (overlayRowConditionalLaw P fee hfee actualTruth)).map
        (overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth) =
      simulatorSourceReportedDrawLaw P 0 (by norm_num) source hm stage ν := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  rw [overlayCoupledRecordTruth_jointLaw P fee hfee (fun record => record.2.record) hr
    (simulatorDrawLaw P 0 (by norm_num) source hm stage ν) actualTruth]
  rw [← coupledRecordTruth_jointLaw P (fun record => record.2.record) hr
    (simulatorDrawLaw P 0 (by norm_num) source hm stage ν) false]
  exact simulatorDraw_reportCouplingLaw P 0 (by norm_num) source hm stage ν hf false

/-- The complete source exit history is retained, including source
allocation/execution/stop/abandonment and the original version serials.
Physical calls remain separate obligations of the actual Native policy. -/
theorem overlayDraw_stageExitCouplingLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod
      (overlayRowConditionalLaw P fee hfee actualTruth)).map
      (fun sample => sourceDrawStageExit source stage
        (overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth sample)) =
      sourceDirectStageExitLaw P 0 (by norm_num) source hm stage ν := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  change ((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod
    (overlayRowConditionalLaw P fee hfee actualTruth)).map
      (sourceDrawStageExit source stage ∘
        overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth) = _
  rw [← Measure.map_map (measurable_sourceDrawStageExit source hm stage)
    (measurable_overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) hr actualTruth),
    overlayDraw_reportCouplingLaw P fee hfee source hm stage ν hf actualTruth,
    simulatorSourceReportedDrawLaw_stageExit]

end PDROC

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- None is still genuine nonreturn. No mark can create a virtual report
for this branch, and old stop/abandonment records are retained unchanged. -/
noncomputable def overlayOptionalStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance)) ×
      (OverlayStageCoins × P.experiment.Tape)) : Seed × EntryHistory P.sharedInstance :=
  sourceOptionalDrawStageExit source stage
    (overlayCoupledRecordTruth P fee hfee (fun record => simulatorDrawRecord record.2) actualTruth sample)

set_option maxHeartbeats 800000 in
theorem measurable_overlayOptionalStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (overlayOptionalStageExit P fee hfee source stage actualTruth) := by
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      Option (SimulatorDraw P.sharedInstance) => simulatorDrawRecord record.2) :=
    (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp measurable_snd
  exact (measurable_sourceOptionalDrawStageExit source hm stage).comp
    (measurable_overlayCoupledRecordTruth P fee hfee
      (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
        simulatorDrawRecord record.2) hr actualTruth)

noncomputable def overlaySampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (actualTruth : Bool)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × P.experiment.Tape)) : Seed × EntryHistory P.sharedInstance :=
  overlayOptionalStageExit P fee hfee source stage actualTruth
    ((sample.1.1, simulatorDrawAt P 0 (by norm_num) source stage sample.1.1.1 sample.1.1.2 sample.1.2), sample.2)

theorem measurable_overlaySampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (actualTruth : Bool) :
    Measurable (overlaySampledStageExit P fee hfee source stage actualTruth) :=
  (measurable_overlayOptionalStageExit P fee hfee source hm stage actualTruth).comp
    ((measurable_fst.prodMk (measurable_simulatorDrawAt P 0 (by norm_num) source hm stage)).prodMap measurable_id)

set_option maxHeartbeats 800000 in
/-- Real auxiliary-tape sampling followed by the independent record-aware
MAP/FP row gives the original free source's complete stage-exit law for
each actual truth. The original input's full bill will discharge hf later. -/
theorem overlaySampledStageExit_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) (actualTruth : Bool) :
    ((ν.prod (auxiliaryTapeLaw P)).prod (overlayRowConditionalLaw P fee hfee actualTruth)).map
      (overlaySampledStageExit P fee hfee source stage actualTruth) =
      (sourceDirectStageExitLaw P 0 (by norm_num) source hm stage ν).map
        (fun result => (result.1, some result.2)) := by
  let sampleDraw := fun sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape =>
    (sample.1, simulatorDrawAt P 0 (by norm_num) source stage sample.1.1 sample.1.2 sample.2)
  let embed := fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
    (record.1, some record.2)
  let endpoint := overlayRowConditionalLaw P fee hfee actualTruth
  have hs : Measurable sampleDraw := measurable_fst.prodMk
    (measurable_simulatorDrawAt P 0 (by norm_num) source hm stage)
  have he : Measurable embed := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp
      measurable_snd)
  have ho := measurable_overlayOptionalStageExit P fee hfee source hm stage actualTruth
  have hmSome : Measurable (fun result : Seed × List (VisibleEvent P.sharedInstance) =>
      (result.1, (some result.2 : EntryHistory P.sharedInstance))) :=
    measurable_fst.prodMk ((measurable_of_countable
      (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp measurable_snd)
  have hr : Measurable (fun record : (Seed × List (VisibleEvent P.sharedInstance)) ×
      SimulatorDraw P.sharedInstance => record.2.record) :=
    (measurable_of_countable (fun draw : SimulatorDraw P.sharedInstance => draw.record)).comp measurable_snd
  have hc := (measurable_sourceDrawStageExit source hm stage).comp
    (measurable_overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) hr actualTruth)
  have hfirst := Measure.map_prod_map (ν.prod (auxiliaryTapeLaw P)) endpoint hs
    (measurable_id : Measurable (id : OverlayStageCoins × P.experiment.Tape → _))
  rw [Measure.map_id] at hfirst
  have hsecond := Measure.map_prod_map (simulatorDrawLaw P 0 (by norm_num) source hm stage ν) endpoint he
    (measurable_id : Measurable (id : OverlayStageCoins × P.experiment.Tape → _))
  rw [Measure.map_id] at hsecond
  have hdraw : (ν.prod (auxiliaryTapeLaw P)).map sampleDraw =
      (simulatorDrawLaw P 0 (by norm_num) source hm stage ν).map embed :=
    simulatorDrawAt_auxiliaryTape_law P 0 (by norm_num) source hm stage ν hf
  calc
    _ = (((ν.prod (auxiliaryTapeLaw P)).map sampleDraw).prod endpoint).map
        (overlayOptionalStageExit P fee hfee source stage actualTruth) := by
      exact (Measure.map_map ho (hs.prodMap measurable_id)).symm.trans
        (congrArg (fun μ => μ.map (overlayOptionalStageExit P fee hfee source stage actualTruth)) hfirst.symm)
    _ = (((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).map embed).prod endpoint).map
        (overlayOptionalStageExit P fee hfee source stage actualTruth) := by rw [hdraw]
    _ = ((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod endpoint).map
        (fun sample => let result := sourceDrawStageExit source stage (overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth sample); (result.1, some result.2)) := by
      rw [hsecond, Measure.map_map ho (he.prodMap measurable_id)]
      rfl
    _ = (((simulatorDrawLaw P 0 (by norm_num) source hm stage ν).prod endpoint).map
        (fun sample => sourceDrawStageExit source stage
          (overlayCoupledRecordTruth P fee hfee (fun record => record.2.record) actualTruth sample))).map
        (fun result => (result.1, some result.2)) := (Measure.map_map hmSome hc).symm
    _ = _ := by rw [overlayDraw_stageExitCouplingLaw P fee hfee source hm stage ν hf actualTruth]

end PDROC

namespace PDROC

universe u v w

/-- Mix the original actual truth with its original stage prior. This
generic row version requires no assumption about how the row is encoded. -/
theorem lintegral_overlayRowWorldLaw_of_conditional_constant
    {Row : Type w} [MeasurableSpace Row] (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (rowLaw : Measure Row) [SFinite rowLaw]
    (f : Row × (Bool × P.experiment.Tape) → ℝ≥0∞) (hf : Measurable f) (value : ℝ≥0∞)
    (hvalue : ∀ truth, (∫⁻ pair, f (pair.1, (truth, pair.2))
      ∂rowLaw.prod (P.experiment.tapeLaw truth)) = value) :
    (∫⁻ pair, f pair ∂rowLaw.prod ((P.input fee hfee).stageLaw stage)) = value := by
  have hfixed (truth : Bool) :
      (∫⁻ pair, f pair ∂rowLaw.prod ((Measure.dirac truth).prod (P.experiment.tapeLaw truth))) = value := by
    have ht : Measurable (fun tape : P.experiment.Tape => (truth, tape)) :=
      measurable_const.prodMk measurable_id
    have hmap := Measure.map_prod_map rowLaw (P.experiment.tapeLaw truth) measurable_id ht
    rw [Measure.map_id] at hmap
    rw [Measure.dirac_prod, hmap, lintegral_map hf (measurable_id.prodMap ht)]
    exact hvalue truth
  change (∫⁻ pair, f pair ∂rowLaw.prod
    (P.experiment.priorMass true • (Measure.dirac true).prod (P.experiment.tapeLaw true) +
      P.experiment.priorMass false • (Measure.dirac false).prod (P.experiment.tapeLaw false))) = value
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, hfixed, hfixed]
  change P.experiment.priorMass true * value + P.experiment.priorMass false * value = value
  rw [← add_mul]
  have hs : P.experiment.priorMass true + P.experiment.priorMass false = 1 := by
    simpa only [Fintype.sum_bool] using P.experiment.priorMass_sum
  rw [hs, one_mul]

theorem prod_overlayRowWorldLaw_map_of_conditional_constant
    {Source : Type u} {Target : Type v} {Row : Type w}
    [MeasurableSpace Source] [MeasurableSpace Target] [MeasurableSpace Row]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (ρ : Measure Source) [SFinite ρ] (rowLaw : Measure Row) [SFinite rowLaw]
    (f : Source × (Row × (Bool × P.experiment.Tape)) → Target) (hf : Measurable f)
    (law : Measure Target)
    (hconditional : ∀ truth,
      (ρ.prod (rowLaw.prod (P.experiment.tapeLaw truth))).map
        (fun sample => f (sample.1, (sample.2.1, (truth, sample.2.2)))) = law) :
    (ρ.prod (rowLaw.prod ((P.input fee hfee).stageLaw stage))).map f = law := by
  let endpoint : Measure (Row × (Bool × P.experiment.Tape)) :=
    rowLaw.prod ((P.input fee hfee).stageLaw stage)
  let : SFinite endpoint := by
    dsimp only [endpoint]
    change SFinite (rowLaw.prod ((P.input fee hfee).stageLaw stage))
    infer_instance
  change (ρ.prod endpoint).map f = law
  apply Measure.ext
  intro A hA
  let indicator := A.indicator (fun _ : Target => (1 : ℝ≥0∞))
  have hi : Measurable indicator := measurable_const.indicator hA
  have hif : Measurable (fun sample => indicator (f sample)) := hi.comp hf
  have hg : Measurable (fun endpoint : Row × (Bool × P.experiment.Tape) =>
      ∫⁻ source, indicator (f (source, endpoint)) ∂ρ) := hif.lintegral_prod_left'
  rw [← lintegral_indicator_one hA]
  change (∫⁻ result, indicator result ∂(ρ.prod endpoint).map f) = law A
  rw [lintegral_map hi hf, lintegral_prod_symm _ hif.aemeasurable]
  apply lintegral_overlayRowWorldLaw_of_conditional_constant P fee hfee stage rowLaw _ hg
  intro truth
  have hm : Measurable (fun sample : Source × (Row × P.experiment.Tape) =>
      f (sample.1, (sample.2.1, (truth, sample.2.2)))) :=
    hf.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd))))
  have ht : Measurable (fun sample : Source × (Row × P.experiment.Tape) =>
      indicator (f (sample.1, (sample.2.1, (truth, sample.2.2))))) := hi.comp hm
  calc
    _ = ∫⁻ sample : Source × (Row × P.experiment.Tape),
        indicator (f (sample.1, (sample.2.1, (truth, sample.2.2))))
          ∂ρ.prod (rowLaw.prod (P.experiment.tapeLaw truth)) :=
      (lintegral_prod_symm (μ := ρ) (ν := rowLaw.prod (P.experiment.tapeLaw truth)) _ ht.aemeasurable).symm
    _ = ∫⁻ result, indicator result ∂((ρ.prod (rowLaw.prod (P.experiment.tapeLaw truth))).map
          (fun sample => f (sample.1, (sample.2.1, (truth, sample.2.2))))) := (lintegral_map hi hm).symm
    _ = _ := by rw [hconditional truth]; exact lintegral_indicator_one hA

variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def overlayMixedSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × (Bool × P.experiment.Tape))) : Seed × EntryHistory P.sharedInstance :=
  overlaySampledStageExit P fee hfee source stage sample.2.2.1
    (sample.1, (sample.2.1, sample.2.2.2))

set_option maxHeartbeats 800000 in
theorem measurable_overlayMixedSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayMixedSampledStageExit P fee hfee source stage) := by
  let build := fun pair : (((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × P.experiment.Tape)) × Bool =>
    overlaySampledStageExit P fee hfee source stage pair.2 pair.1
  have hb : Measurable build := measurable_from_prod_countable_left
    (fun truth => measurable_overlaySampledStageExit P fee hfee source hm stage truth)
  have hp : Measurable (fun sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × (Bool × P.experiment.Tape)) =>
      ((sample.1, (sample.2.1, sample.2.2.2)), sample.2.2.1)) :=
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_snd)
  exact hb.comp hp

/-- The actual world retains its original truth/tape law. Under that law,
the genuinely sampled auxiliary record and fresh record-aware coins give
exactly the source full-stage exit law, with all nonreturn/stop branches. -/
theorem overlayMixedSampledStageExit_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P 0 (by norm_num) source hm stage) truth ≠ ⊤) :
    ((ν.prod (auxiliaryTapeLaw P)).prod
      ((overlayPaidStageCoinsLaw P fee hfee).prod ((P.input fee hfee).stageLaw stage))).map
        (overlayMixedSampledStageExit P fee hfee source stage) =
      (sourceDirectStageExitLaw P 0 (by norm_num) source hm stage ν).map (fun result => (result.1, some result.2)) := by
  apply prod_overlayRowWorldLaw_map_of_conditional_constant P fee hfee stage
    (ν.prod (auxiliaryTapeLaw P)) (overlayPaidStageCoinsLaw P fee hfee)
    (overlayMixedSampledStageExit P fee hfee source stage)
    (measurable_overlayMixedSampledStageExit P fee hfee source hm stage)
  intro truth
  exact overlaySampledStageExit_law P fee hfee source hm stage ν hf truth

end PDROC
