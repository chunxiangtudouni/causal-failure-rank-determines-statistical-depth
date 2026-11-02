module

public import PaperProofs.Paid.PDROC_SimulatorObservation_001
public import Mathlib.Algebra.Order.Floor.Extended

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem stageObservationBill_eq_runStageObservationBill (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World) :
    P.stageObservationBill fee hfee C accounting rule stage sample =
      runStageObservationBill (P.input fee hfee) C.val .uncapped accounting rule stage sample := by
  unfold PaperProofs.Paid.Parameters.stageObservationBill PaperProofs.Paid.Parameters.paidRunReviewCount
    runStageObservationBill
  rw [ENat.toENNReal_iSup, ENNReal.mul_iSup]
  rfl

noncomputable def simulatorEntryAuxEndpoint (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    ((Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) ×
      (Bool × (Bool × P.binarySymmetric.experiment.Tape)) :=
  ((simulatorVirtualEntryGate P fee hfee C accounting source stage sample, sample.1.2.1 stage),
    simulatorFreshEndpoint P fee hfee stage sample)

theorem measurable_simulatorEntryAuxEndpoint (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorEntryAuxEndpoint P fee hfee C accounting source stage) := by
  have hg : Measurable (simulatorVirtualEntryGate P fee hfee C accounting source stage) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_simulatorVirtualEntry P fee hfee C accounting source hm stage)
  exact (hg.prodMk ((measurable_pi_apply stage).comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))).prodMk
    (by unfold simulatorFreshEndpoint; fun_prop)

theorem simulatorEntryAuxEndpoint_jointLaw_of_entryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (stage : P.sharedInstance.Stage)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEntryAuxEndpoint P fee hfee C accounting source.rule stage) =
      ((sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod (auxiliaryTapeLaw P)).prod
        (simulatorEndpointLaw P fee hfee stage) := by
  let μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)
  let η := (simulatorAllOtherLaw P fee hfee ν stage).map
    (simulatorVirtualEntryFactor P fee hfee C accounting source.rule stage)
  let stageLaw : Measure (Bool × P.binarySymmetric.experiment.Tape) := (P.input fee hfee).stageLaw stage
  let freshLaw : Measure ((P.binarySymmetric.experiment.Tape × Bool) × (Bool × P.binarySymmetric.experiment.Tape)) :=
    ((auxiliaryTapeLaw P).prod fairGuessLaw).prod stageLaw
  let : IsProbabilityMeasure stageLaw := StatisticalInput.stageLaw_probability (P.input fee hfee) stage
  let : IsProbabilityMeasure freshLaw := by
    unfold freshLaw
    infer_instance
  let raw : SimulatorSeed P Seed × (P.input fee hfee).World →
      (Seed × EntryHistory P.sharedInstance) ×
        ((P.binarySymmetric.experiment.Tape × Bool) × (Bool × P.binarySymmetric.experiment.Tape)) := fun sample =>
    (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage sample,
      simulatorFreshStage P fee hfee stage sample)
  have hg : Measurable (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_simulatorVirtualEntry P fee hfee C accounting source.rule source.measurable_rule stage)
  have hm : Measurable raw := hg.prodMk (by
    unfold simulatorFreshStage simulatorCurrentNoise
    fun_prop)
  have hlaw : μ.map raw = η.prod freshLaw :=
    simulatorVirtualEntry_joint_freshStage P fee hfee C accounting source.rule source.measurable_rule ν stage
  have hη := congrArg (fun law => law.map Prod.fst) hlaw
  rw [Measure.map_map measurable_fst hm, Measure.map_fst_prod, measure_univ, one_smul] at hη
  change μ.map (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) = η at hη
  have hη' : η = sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage := hη.symm.trans hentry
  have hp : MeasurePreserving raw μ
      (η.prod freshLaw) := ⟨hm, hlaw⟩
  have h1 := (MeasurePreserving.id η).prod
    (measurePreserving_prodAssoc (auxiliaryTapeLaw P) fairGuessLaw stageLaw)
  have h2 := (measurePreserving_prodAssoc η (auxiliaryTapeLaw P)
    (fairGuessLaw.prod stageLaw)).symm MeasurableEquiv.prodAssoc
  have h := ((h2.comp h1).comp hp).map_eq
  rw [hη'] at h
  exact h

end PDROC


