module

public import PaperProofs.Paid.PDROC_SimulatorLaw_008
public import PaperProofs.Paid.PDROC_SimulatorLaw_013
public import PaperProofs.Paid.PDROC_SimulatorLaw_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def sourceEventualStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hfee).World) :=
  sourceDrawStageExit (sourceForOptionalHistory source.rule) stage
    (sourceEventualReportedDraw P fee hfee C accounting source stage sample)

noncomputable def sourceEventualStageExitSome (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hfee).World) :
    (Seed × EntryHistory P.sharedInstance) × EntryHistory P.sharedInstance :=
  let result := sourceEventualStageExit P fee hfee C accounting source stage sample
  (result.1, some result.2)

theorem measurable_simulatorVirtualEntryGate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorVirtualEntryGate P fee hfee C accounting source stage) :=
  (measurable_fst.comp measurable_fst).prodMk
    (measurable_simulatorVirtualEntry P fee hfee C accounting source hm stage)

noncomputable def simulatorEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    ((((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape))) :=
  ((sourceEventualHistorySeed (simulatorVirtualEntryGate P fee hfee C accounting source stage sample),
    sample.1.2.1 stage), (sample.1.2.2 stage, sample.2 stage))

theorem measurable_simulatorEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorEventualStageSample P fee hfee C accounting source stage) :=
  (((measurable_sourceEventualHistorySeed.comp
      (measurable_simulatorVirtualEntryGate P fee hfee C accounting source hm stage)).prodMk
        ((measurable_pi_apply stage).comp ((measurable_fst.comp measurable_snd).comp measurable_fst))).prodMk
    (((measurable_pi_apply stage).comp ((measurable_snd.comp measurable_snd).comp measurable_fst)).prodMk
      ((measurable_pi_apply stage).comp measurable_snd)))

noncomputable def simulatorEventualStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :=
  simulatorMixedSampledStageExit P fee hfee (sourceForOptionalHistory source) stage
    (simulatorEventualStageSample P fee hfee C accounting source stage sample)

theorem measurable_sourceEventualStageExitSome (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    Measurable (sourceEventualStageExitSome P fee hfee C accounting source stage) := by
  have hh := (measurable_sourceDrawStageExit (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).comp
      (measurable_sourceEventualReportedDraw P fee hfee C accounting source stage)
  exact (measurable_fst.comp hh).prodMk
    ((measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp
      (measurable_snd.comp hh))

theorem measurable_simulatorEventualStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorEventualStageExit P fee hfee C accounting source stage) :=
  (measurable_simulatorMixedSampledStageExit P fee hfee (sourceForOptionalHistory source)
    (measurable_sourceForOptionalHistory source hm) stage).comp
      (measurable_simulatorEventualStageSample P fee hfee C accounting source hm stage)

theorem simulatorWorldLaw_allOther (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorAllOther P fee hfee stage) = simulatorAllOtherLaw P fee hfee ν stage := by
  have hm : Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      (simulatorAllOther P fee hfee stage sample, simulatorFreshStage P fee hfee stage sample)) := by
    unfold simulatorAllOther simulatorFreshStage simulatorOtherNoise simulatorCurrentNoise
    fun_prop
  have h := congrArg (fun μ => μ.map Prod.fst) (simulatorWorldLaw_allOther_freshStage P fee hfee ν stage)
  have hcompose := Measure.map_map (μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)) measurable_fst hm
  have hmassAux : ((auxiliaryTapeLaw P).prod fairGuessLaw) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, mul_one]
  have hmass : (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hmassAux, measure_univ, mul_one]
  have hnoise : SFinite ((((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) :
      Measure ((P.experiment.Tape × Bool) × (Bool × P.experiment.Tape))) := by
    change SFinite ((((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) :
      Measure ((P.binarySymmetric.experiment.Tape × Bool) × (P.input fee hfee).StageSample stage))
    infer_instance
  have hfst : ((simulatorAllOtherLaw P fee hfee ν stage).prod
      (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage))).map
        (Prod.fst : ((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) ×
          ((P.experiment.Tape × Bool) × (Bool × P.experiment.Tape)) → _) =
      ((((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) Set.univ) •
        simulatorAllOtherLaw P fee hfee ν stage := @Measure.map_fst_prod _ _ _ _ _ _ hnoise
  exact hcompose.symm.trans (h.trans (hfst.trans (by rw [hmass, one_smul])))

theorem simulatorVirtualEntryFactor_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    (simulatorAllOtherLaw P fee hfee ν stage).map (simulatorVirtualEntryFactor P fee hfee C accounting source stage) =
      ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorVirtualEntryGate P fee hfee C accounting source stage) := by
  have hf := (measurable_simulatorVirtualEntryGate P fee hfee C accounting source hm stage).comp
    (measurable_completeSimulatorAllOther P fee hfee stage)
  have ho : Measurable (simulatorAllOther P fee hfee stage (Seed := Seed)) := by
    unfold simulatorAllOther simulatorOtherNoise
    fun_prop
  calc
    _ = (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorAllOther P fee hfee stage)).map (simulatorVirtualEntryFactor P fee hfee C accounting source stage) := by
      rw [simulatorWorldLaw_allOther]
    _ = ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        ((simulatorVirtualEntryFactor P fee hfee C accounting source stage) ∘ simulatorAllOther P fee hfee stage) :=
      Measure.map_map hf ho
    _ = _ := by
      apply congrArg (Measure.map · _)
      funext sample
      exact (simulatorVirtualEntryGate_factorization P fee hfee C accounting source stage sample).symm

set_option maxHeartbeats 800000 in
theorem simulatorEventualStageSample_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEventualStageSample P fee hfee C accounting source.rule stage) =
      ((sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage).prod (auxiliaryTapeLaw P)).prod
        (simulatorEndpointLaw P fee hfee stage) := by
  let factor := simulatorVirtualEntryFactor P fee hfee C accounting source.rule stage
  let augment := sourceEventualHistorySeed (I := P.sharedInstance) (Seed := Seed)
  have hf : Measurable factor :=
    (measurable_simulatorVirtualEntryGate P fee hfee C accounting source.rule source.measurable_rule stage).comp
      (measurable_completeSimulatorAllOther P fee hfee stage)
  have ha : Measurable augment := measurable_sourceEventualHistorySeed
  let recordGate := Prod.map (augment ∘ factor) (id : P.experiment.Tape → P.experiment.Tape)
  have hg : Measurable recordGate := (ha.comp hf).prodMap measurable_id
  have h := simulatorWorldLaw_recordGate_freshEndpoint P fee hfee ν stage recordGate hg
  have hfactor : (simulatorAllOtherLaw P fee hfee ν stage).map factor =
      sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage :=
    (simulatorVirtualEntryFactor_law P fee hfee C accounting source.rule source.measurable_rule ν stage).trans hentry
  have haug : (simulatorAllOtherLaw P fee hfee ν stage).map (augment ∘ factor) =
      sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage := by
    rw [← Measure.map_map ha hf, hfactor]
    rfl
  have hp := Measure.map_prod_map (simulatorAllOtherLaw P fee hfee ν stage) (auxiliaryTapeLaw P)
    (ha.comp hf) (measurable_id : Measurable (id : P.experiment.Tape → P.experiment.Tape))
  have hid : (auxiliaryTapeLaw P).map (id : P.experiment.Tape → P.experiment.Tape) = auxiliaryTapeLaw P := Measure.map_id
  have hp' := (congrArg (fun τ : Measure P.experiment.Tape =>
    ((simulatorAllOtherLaw P fee hfee ν stage).map (augment ∘ factor)).prod τ) hid).symm.trans hp
  rw [haug] at hp'
  have hpoint : (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      (recordGate (simulatorRecordBase P fee hfee stage sample), simulatorFreshEndpoint P fee hfee stage sample)) =
      simulatorEventualStageSample P fee hfee C accounting source.rule stage := by
    funext sample
    change ((augment (factor (simulatorAllOther P fee hfee stage sample)), _), _) = _
    exact Prod.ext (Prod.ext (congrArg augment
      (simulatorVirtualEntryGate_factorization P fee hfee C accounting source.rule stage sample).symm) rfl) rfl
  rw [hpoint] at h
  exact h.trans (congrArg (fun τ : Measure
    (((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) =>
      τ.prod (simulatorEndpointLaw P fee hfee stage)) hp'.symm)

theorem sourceEventualStageExitSome_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map (sourceEventualStageExitSome P fee hfee C accounting source stage) =
      (sourceDirectStageExitLaw P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)).map
            (fun result => (result.1, some result.2)) := by
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  have he := measurable_sourceDrawStageExit wrapped hm stage
  have hs : Measurable (fun result : (Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance) =>
      (result.1, (some result.2 : EntryHistory P.sharedInstance))) :=
    measurable_fst.prodMk ((measurable_of_countable (some : List (VisibleEvent P.sharedInstance) →
      EntryHistory P.sharedInstance)).comp measurable_snd)
  calc
    _ = (((P.input fee hfee).seededWorldLaw ν).map
        (sourceEventualReportedDraw P fee hfee C accounting source stage)).map
          (fun record => let result := sourceDrawStageExit wrapped stage record; (result.1, some result.2)) :=
      (Measure.map_map (hs.comp he) (measurable_sourceEventualReportedDraw P fee hfee C accounting source stage)).symm
    _ = ((simulatorSourceReportedDrawLaw P fee hfee wrapped hm stage
        (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)).map
          (sourceDrawStageExit wrapped stage)).map (fun result => (result.1, some result.2)) := by
      rw [sourceEventualReportedDraw_law, Measure.map_map hs he]
      rfl
    _ = _ := by rw [simulatorSourceReportedDrawLaw_stageExit]

/-- The complete generated stage-exit law follows from the current entry
law alone. The local sample finiteness comes from the original full bill. -/
theorem simulatorEventualStageExit_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEventualStageExit P fee hfee C accounting source.rule stage) =
      ((P.input fee hfee).seededWorldLaw ν).map (sourceEventualStageExitSome P fee hfee C accounting source stage) := by
  have hm := measurable_simulatorMixedSampledStageExit P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
  calc
    _ = (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorEventualStageSample P fee hfee C accounting source.rule stage)).map
          (simulatorMixedSampledStageExit P fee hfee (sourceForOptionalHistory source.rule) stage) :=
      (Measure.map_map hm (measurable_simulatorEventualStageSample P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = (sourceDirectStageExitLaw P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)).map
            (fun result => (result.1, some result.2)) := by
      rw [simulatorEventualStageSample_law_of_entryLaw P fee hfee C accounting source ν stage hentry]
      exact simulatorMixedSampledStageExit_law P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage _
          (sourceEventualDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage hfinite)
    _ = _ := (sourceEventualStageExitSome_law P fee hfee C accounting source ν stage).symm

end PDROC
