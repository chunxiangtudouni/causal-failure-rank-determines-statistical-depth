module

public import PaperProofs.Paid.PDROC_SimulatorObservation_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def simulatorOptionalEndpointCharge (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (pair : ((Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape))) : ℝ≥0∞ :=
  let record := simulatorOptionalHistoryRecord P fee hfee source stage pair.1
  if record.decision.isSome = true then simulatorEndpointCharge P record pair.2 else 0

theorem measurable_simulatorOptionalEndpointCharge (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorOptionalEndpointCharge P fee hfee source stage) := by
  have hfamily : Measurable (fun pair : AuxiliaryRecord × (Bool × (Bool × P.experiment.Tape)) =>
      if pair.1.decision.isSome = true then simulatorEndpointCharge P pair.1 pair.2 else 0) := by
    apply measurable_from_prod_countable_right
    intro record
    by_cases hd : record.decision.isSome = true
    · simpa only [hd, ↓reduceIte] using measurable_simulatorEndpointCharge P record
    · simpa only [hd, Bool.false_eq_true, ↓reduceIte] using (measurable_const : Measurable
        (fun _ : Bool × (Bool × P.experiment.Tape) => (0 : ℝ≥0∞)))
  have hp : Measurable (fun pair : ((Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape)) =>
      (simulatorOptionalHistoryRecord P fee hfee source stage pair.1, pair.2)) :=
    ((measurable_simulatorOptionalHistoryRecord P fee hfee source hm stage).comp measurable_fst).prodMk measurable_snd
  exact hfamily.comp hp
theorem simulatorOptionalEndpointCharge_integral (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (η : Measure (Seed × EntryHistory P.sharedInstance)) [SFinite η] :
    (∫⁻ pair, simulatorOptionalEndpointCharge P fee hfee source stage pair
      ∂(η.prod (auxiliaryTapeLaw P)).prod (simulatorEndpointLaw P fee hfee stage)) =
      ∫⁻ pair, simulatorRecordWritingMean P (simulatorOptionalHistoryRecord P fee hfee source stage pair)
        ∂η.prod (auxiliaryTapeLaw P) := by
  let ε : Measure (Bool × (Bool × P.experiment.Tape)) := simulatorEndpointLaw P fee hfee stage
  let : IsProbabilityMeasure ε := simulatorEndpointLaw_probability P fee hfee stage
  change (∫⁻ pair : ((Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) ×
    (Bool × (Bool × P.experiment.Tape)), simulatorOptionalEndpointCharge P fee hfee source stage pair
      ∂(η.prod (auxiliaryTapeLaw P)).prod ε) = _
  rw [lintegral_prod _ (measurable_simulatorOptionalEndpointCharge P fee hfee source hm stage).aemeasurable]
  apply lintegral_congr
  intro pair
  by_cases hd : (simulatorOptionalHistoryRecord P fee hfee source stage pair).decision.isSome = true
  · simpa only [simulatorOptionalEndpointCharge, simulatorRecordWritingMean, hd, ↓reduceIte, ε] using
      simulatorEndpointLaw_charge P fee hfee stage (simulatorOptionalHistoryRecord P fee hfee source stage pair)
  · simp only [simulatorOptionalEndpointCharge, simulatorRecordWritingMean, hd, Bool.false_eq_true, ↓reduceIte, lintegral_zero]

theorem simulator_runStageBill_eq_optionalEndpointCharge (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) :
    runStageObservationBill (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage sample =
      simulatorOptionalEndpointCharge P fee hfee source stage
        (simulatorEntryAuxEndpoint P fee hfee C accounting source stage sample) := by
  cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample with
  | none =>
    have hrec : simulatorOptionalHistoryRecord P fee hfee source stage
        (simulatorEntryAuxEndpoint P fee hfee C accounting source stage sample).1 = simulatorEmptyRecord := by
      change simulatorOptionalHistoryRecord P fee hfee source stage
        ((sample.1.1, (entryHistory (P.input fee hfee) C.val .uncapped accounting
          (simulatorRule P fee hfee source) stage sample).map (simulatorShadow P fee hfee source sample.1)), _) = _
      rw [he, Option.map_none]
      exact simulatorOptionalHistoryRecord_none P fee hfee source hm stage _ _
    rw [runStageObservationBill_zero_of_no_entry (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (simulatorRule_legal P fee hfee C accounting source) stage sample he]
    simp only [simulatorOptionalEndpointCharge, hrec, simulatorEmptyRecord, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
  | some entry =>
    let record := (simulatorData P fee hfee source).record sample.1 stage entry
    have hrec : simulatorOptionalHistoryRecord P fee hfee source stage
        (simulatorEntryAuxEndpoint P fee hfee C accounting source stage sample).1 = record := by
      change simulatorOptionalHistoryRecord P fee hfee source stage
        ((sample.1.1, (entryHistory (P.input fee hfee) C.val .uncapped accounting
          (simulatorRule P fee hfee source) stage sample).map (simulatorShadow P fee hfee source sample.1)), _) = _
      rw [he, Option.map_some]
      exact simulatorOptionalHistoryRecord_some P fee hfee source stage sample.1.1
        (simulatorShadow P fee hfee source sample.1 entry) (sample.1.2.1 stage)
    change simulatorOptionalHistoryRecord P fee hfee source stage
      (simulatorVirtualEntryGate P fee hfee C accounting source stage sample, sample.1.2.1 stage) = record at hrec
    have hb := simulator_boundaryStage_pointwise P fee hfee C accounting source sample.1 sample.2 hfinite stage entry he
    change match record.decision with | none => _ | some decision => _ at hb
    cases hd : record.decision with
    | none =>
      rw [hd] at hb
      have hz : P.stageObservationBill fee hfee C accounting (simulatorRule P fee hfee source) stage sample = 0 := by
        unfold PaperProofs.Paid.Parameters.stageObservationBill
        rw [hb.2]
        simp
      rw [← stageObservationBill_eq_runStageObservationBill P fee hfee C accounting
        (simulatorRule P fee hfee source) stage sample, hz]
      simp only [simulatorOptionalEndpointCharge, simulatorEntryAuxEndpoint, hrec, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    | some decision =>
      have hc : sample ∈ P.recordCell fee hfee C accounting (simulatorRule P fee hfee source)
          (simulatorData P fee hfee source) stage record Set.univ := ⟨entry, he, Set.mem_univ _, rfl⟩
      have hv := (simulator_cell_writing_observables P fee hfee C accounting source sample hfinite
        stage record decision hd Set.univ hc).1
      have hv' := (stageObservationBill_eq_runStageObservationBill P fee hfee C accounting
        (simulatorRule P fee hfee source) stage sample).symm.trans hv
      simpa only [simulatorOptionalEndpointCharge, hrec, hd, Option.isSome_some, ↓reduceIte,
        simulatorEntryAuxEndpoint] using hv'

end PDROC



