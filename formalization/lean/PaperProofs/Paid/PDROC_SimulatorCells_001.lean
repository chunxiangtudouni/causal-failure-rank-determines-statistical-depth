module

public import PaperProofs.Paid.PDROC_SimulatorLaw_004
public import PaperProofs.Paid.PDROC_SimulatorRecords_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

instance simulatorEntryRecordOptionMeasurable (I : Instance) :
    MeasurableSpace (Option (List (VisibleEvent I) × AuxiliaryRecord)) := ⊤
instance simulatorEntryRecordOptionSingleton (I : Instance) :
    MeasurableSingletonClass (Option (List (VisibleEvent I) × AuxiliaryRecord)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

abbrev SimulatorRecordGate (P : PaperProofs.Paid.Parameters) (Seed : Type u) :=
  Seed × Option (List (VisibleEvent P.sharedInstance) × AuxiliaryRecord)

variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def simulatorBuildRecordGate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (pair : (Seed × P.experiment.Tape) × EntryHistory P.sharedInstance) : SimulatorRecordGate P Seed :=
  (pair.1.1, pair.2.map (fun entry => (entry,
    simulatorDrawRecord (simulatorDrawAt P fee hfee source stage pair.1.1 entry pair.1.2))))

theorem measurable_simulatorBuildRecordGate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorBuildRecordGate P fee hfee source stage) := by
  apply measurable_from_prod_countable_left
  intro entry
  cases entry with
  | none => exact measurable_fst.prodMk measurable_const
  | some history =>
    have hp : Measurable (fun pair : Seed × P.experiment.Tape => ((pair.1, history), pair.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have hd := (measurable_simulatorDrawAt P fee hfee source hm stage).comp hp
    change Measurable (fun pair : Seed × P.experiment.Tape =>
      simulatorDrawAt P fee hfee source stage pair.1 history pair.2) at hd
    have hr := (measurable_of_countable (fun draw : Option (SimulatorDraw P.sharedInstance) =>
      some (history, simulatorDrawRecord draw))).comp hd
    exact measurable_fst.prodMk hr

noncomputable def simulatorGeneratedRecordGate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) : SimulatorRecordGate P Seed :=
  simulatorBuildRecordGate P fee hfee source stage
    ((sample.1.1, sample.1.2.1 stage), simulatorVirtualEntry P fee hfee C accounting source stage sample)

noncomputable def simulatorRecordGateFactor (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (base : ((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) × P.experiment.Tape) :
    SimulatorRecordGate P Seed :=
  simulatorBuildRecordGate P fee hfee source stage
    ((base.1.1.1, base.2), (simulatorVirtualEntryFactor P fee hfee C accounting source stage base.1).2)

theorem simulatorGeneratedRecordGate_factorization (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    simulatorGeneratedRecordGate P fee hfee C accounting source stage sample =
      simulatorRecordGateFactor P fee hfee C accounting source stage (simulatorRecordBase P fee hfee stage sample) := by
  have h := congrArg Prod.snd (simulatorVirtualEntryGate_factorization P fee hfee C accounting source stage sample)
  change simulatorVirtualEntry P fee hfee C accounting source stage sample = _ at h
  unfold simulatorGeneratedRecordGate simulatorRecordGateFactor
  rw [h]
  rfl

theorem measurable_simulatorRecordGateFactor (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorRecordGateFactor P fee hfee C accounting source stage) := by
  have hv : Measurable (simulatorVirtualEntryFactor P fee hfee C accounting source stage) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_simulatorVirtualEntry P fee hfee C accounting source hm stage)).comp
      (measurable_completeSimulatorAllOther P fee hfee stage)
  exact (measurable_simulatorBuildRecordGate P fee hfee source hm stage).comp
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd).prodMk
      (hv.snd.comp measurable_fst))

theorem measurable_simulatorGeneratedRecordGate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorGeneratedRecordGate P fee hfee C accounting source stage) := by
  have hp : Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      ((sample.1.1, sample.1.2.1 stage), simulatorVirtualEntry P fee hfee C accounting source stage sample)) :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_apply stage).comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))).prodMk
      (measurable_simulatorVirtualEntry P fee hfee C accounting source hm stage)
  exact (measurable_simulatorBuildRecordGate P fee hfee source hm stage).comp hp
noncomputable def simulatorRecordGateCell (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) : Set (SimulatorRecordGate P Seed) :=
  {gate | ∃ entry, gate.2 = some (entry, record) ∧ (gate.1, entry) ∈ B}

theorem measurableSet_simulatorRecordGateCell (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) (hB : MeasurableSet B) :
    MeasurableSet (simulatorRecordGateCell P record B) := by
  have hs : simulatorRecordGateCell P record B = ⋃ entry : List (VisibleEvent P.sharedInstance),
      {gate : SimulatorRecordGate P Seed | gate.2 = some (entry, record)} ∩
        {gate | (gate.1, entry) ∈ B} := by ext gate; simp [simulatorRecordGateCell]
  rw [hs]
  exact MeasurableSet.iUnion (fun entry =>
    ((measurableSet_singleton (some (entry, record))).preimage measurable_snd).inter
      (hB.preimage (measurable_fst.prodMk measurable_const)))

omit [MeasurableSpace Seed] in
theorem simulator_recordCell_eq_gate_preimage (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) :
    P.recordCell fee hfee C accounting (simulatorRule P fee hfee source) (simulatorData P fee hfee source) stage record B =
      (simulatorGeneratedRecordGate P fee hfee C accounting source stage) ⁻¹' simulatorRecordGateCell P record B := by
  ext sample
  cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample with
  | none => simp [PaperProofs.Paid.Parameters.recordCell, he, simulatorGeneratedRecordGate,
      simulatorBuildRecordGate, simulatorVirtualEntry, simulatorRecordGateCell]
  | some entry =>
    simp [PaperProofs.Paid.Parameters.recordCell, he, simulatorGeneratedRecordGate, simulatorBuildRecordGate,
      simulatorVirtualEntry, simulatorRecordGateCell, simulatorData, simulatorSeedDraw, and_comm]

noncomputable def simulatorRecordGateLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) (stage : P.sharedInstance.Stage) :
    Measure (SimulatorRecordGate P Seed) :=
  (((simulatorAllOtherLaw P fee hfee ν stage).prod (auxiliaryTapeLaw P)).map
    (simulatorRecordGateFactor P fee hfee C accounting source stage))

theorem simulatorGeneratedRecordGate_jointLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (simulatorGeneratedRecordGate P fee hfee C accounting source stage sample,
        simulatorFreshEndpoint P fee hfee stage sample)) =
      (simulatorRecordGateLaw P fee hfee C accounting source ν stage).prod
        (PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  have h := simulatorWorldLaw_recordGate_freshEndpoint P fee hfee ν stage
    (simulatorRecordGateFactor P fee hfee C accounting source stage)
    (measurable_simulatorRecordGateFactor P fee hfee C accounting source hm stage)
  simpa only [← simulatorGeneratedRecordGate_factorization, simulatorRecordGateLaw] using h

end PDROC

