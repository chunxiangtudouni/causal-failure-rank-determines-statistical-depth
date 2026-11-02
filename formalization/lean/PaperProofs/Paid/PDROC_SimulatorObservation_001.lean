module

public import PaperProofs.Paid.PDROC_EventualEntry_002
public import PaperProofs.Paid.PDROC_SimulatorCells_005
public import PaperProofs.Paid.PDROC_LocalRecord_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

noncomputable def simulatorRecordWritingMean (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) : ℝ≥0∞ :=
  if record.decision.isSome = true then ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) else 0

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulatorAuxiliaryWritingMean_le_sourceCharge (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    (∫⁻ pair, simulatorRecordWritingMean P (simulatorDrawRecord
      (simulatorDrawAt P fee hfee source stage pair.1.1 pair.1.2 pair.2)) ∂ν.prod (auxiliaryTapeLaw P)) ≤
      P.binarySymmetric.experiment.bayesObservationCharge ν (simulatorLocalTest P fee hfee source hm stage) := by
  let sampleDraw := fun pair : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
    (pair.1, simulatorDrawAt P fee hfee source stage pair.1.1 pair.1.2 pair.2)
  let embed := fun draw : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance =>
    (draw.1, some draw.2)
  let value := fun draw : (Seed × List (VisibleEvent P.sharedInstance)) × Option (SimulatorDraw P.sharedInstance) =>
    simulatorRecordWritingMean P (simulatorDrawRecord draw.2)
  have hv : Measurable value := (measurable_of_countable (fun draw : Option (SimulatorDraw P.sharedInstance) =>
    simulatorRecordWritingMean P (simulatorDrawRecord draw))).comp measurable_snd
  have hs : Measurable sampleDraw := measurable_fst.prodMk (measurable_simulatorDrawAt P fee hfee source hm stage)
  have he : Measurable embed := measurable_fst.prodMk
    ((measurable_of_countable (some : SimulatorDraw P.sharedInstance → Option (SimulatorDraw P.sharedInstance))).comp measurable_snd)
  have hdraw : (ν.prod (auxiliaryTapeLaw P)).map sampleDraw =
      (simulatorDrawLaw P fee hfee source hm stage ν).map embed :=
    simulatorDrawAt_auxiliaryTape_law P fee hfee source hm stage ν hf
  have hmap := congrArg (fun law => ∫⁻ draw, value draw ∂law) hdraw
  rw [lintegral_map hv hs, lintegral_map hv he] at hmap
  calc
    _ = ∫⁻ draw, simulatorRecordWritingMean P draw.2.record ∂simulatorDrawLaw P fee hfee source hm stage ν := hmap
    _ ≤ ∫⁻ draw, ENNReal.ofReal (P.binarySymmetric.endpointCharge draw.2.record.level : ℝ)
        ∂simulatorDrawLaw P fee hfee source hm stage ν := by
      apply lintegral_mono
      intro draw
      dsimp only [simulatorRecordWritingMean]
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = _ := (simulatorDrawLaw_endpointCharge_mean P fee hfee source hm stage ν hf).symm

noncomputable def simulatorOptionalHistoryRecord (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (pair : (Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) : AuxiliaryRecord :=
  simulatorDrawRecord (simulatorDrawAt P fee hfee (sourceForOptionalHistory source) stage
    pair.1 (pair.1.2.getD []) pair.2)

theorem measurable_simulatorOptionalHistoryRecord (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorOptionalHistoryRecord P fee hfee source stage) := by
  have hp : Measurable (fun pair : (Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape =>
      (sourceEventualHistorySeed pair.1, pair.2)) := measurable_sourceEventualHistorySeed.prodMap measurable_id
  exact (measurable_of_countable (simulatorDrawRecord (I := P.sharedInstance))).comp
    ((measurable_simulatorDrawAt P fee hfee (sourceForOptionalHistory source)
      (measurable_sourceForOptionalHistory source hm) stage).comp hp)

omit [MeasurableSpace Seed] in
theorem simulatorOptionalHistoryRecord_some (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : Seed) (entry : List (VisibleEvent P.sharedInstance)) (tape : P.binarySymmetric.experiment.Tape) :
    simulatorOptionalHistoryRecord P fee hfee source stage ((seed, some entry), tape) =
      simulatorDrawRecord (simulatorDrawAt P fee hfee source stage seed entry tape) := by
  simp only [simulatorOptionalHistoryRecord, simulatorDrawAt, headExitStop, simulatorPrewriteRule,
    sourceForOptionalHistory, Option.getD_some, Option.isSome_some, ↓reduceIte]
  rfl

theorem simulatorOptionalHistoryRecord_none (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (seed : Seed) (tape : P.binarySymmetric.experiment.Tape) :
    simulatorOptionalHistoryRecord P fee hfee source stage ((seed, none), tape) = simulatorEmptyRecord := by
  have hs := sourceEventualEntryTest_stop_none P fee hfee source hm stage seed tape
  change headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P (sourceForOptionalHistory source))
    ((seed, none), []) tape = 0 at hs
  simp only [simulatorOptionalHistoryRecord, Option.getD_none, simulatorDrawAt, hs,
    ENat.zero_ne_top, ↓reduceIte,
    sourceForOptionalHistory, Option.isSome_none, Bool.false_eq_true,
    optionWriteBit, simulatorDrawRecord, Option.map_some, Option.getD_some, simulatorEmptyRecord]
  congr 1
  apply List.eq_nil_iff_length_eq_zero.mpr
  exact (List.length_ofFn (f := fun k : Fin (headExitStop (P.input fee hfee) stage
    (simulatorPrewriteRule P (sourceForOptionalHistory source)) ((seed, none), []) tape).toNat =>
      tape k.val)).trans (congrArg ENat.toNat hs)

theorem simulatorOptionalWritingMean_le_eventualCharge (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    (∫⁻ pair, simulatorRecordWritingMean P (simulatorOptionalHistoryRecord P fee hfee source.rule stage pair)
      ∂(sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod (auxiliaryTapeLaw P)) ≤
      P.binarySymmetric.experiment.bayesObservationCharge
        (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
        (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage) := by
  let η := sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage
  let drawν := sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage
  have hf := sourceEventualDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage hfinite
  have h := simulatorAuxiliaryWritingMean_le_sourceCharge P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage drawν hf
  have hvalue : Measurable (fun pair : ((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
      simulatorRecordWritingMean P (simulatorDrawRecord (simulatorDrawAt P fee hfee
        (sourceForOptionalHistory source.rule) stage pair.1.1 pair.1.2 pair.2))) :=
    (measurable_of_countable (fun draw : Option (SimulatorDraw P.sharedInstance) =>
      simulatorRecordWritingMean P (simulatorDrawRecord draw))).comp
      (measurable_simulatorDrawAt P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage)
  have hmap := Measure.map_prod_map η (auxiliaryTapeLaw P) measurable_sourceEventualHistorySeed
    (measurable_id : Measurable (id : P.binarySymmetric.experiment.Tape → _))
  rw [Measure.map_id] at hmap
  change (η.map sourceEventualHistorySeed).prod (auxiliaryTapeLaw P) = _ at hmap
  change (∫⁻ pair, simulatorRecordWritingMean P (simulatorDrawRecord (simulatorDrawAt P fee hfee
    (sourceForOptionalHistory source.rule) stage pair.1.1 pair.1.2 pair.2))
    ∂(η.map sourceEventualHistorySeed).prod (auxiliaryTapeLaw P)) ≤ _ at h
  rw [hmap, lintegral_map hvalue (measurable_sourceEventualHistorySeed.prodMap measurable_id)] at h
  simpa only [sourceEventualEntryTest, bayesObservationCharge_pullbackSeedTest, sourceEventualDrawSeedLaw,
    simulatorOptionalHistoryRecord, Prod.map_apply', id_eq, sourceEventualHistorySeed, η, drawν] using h

end PDROC




