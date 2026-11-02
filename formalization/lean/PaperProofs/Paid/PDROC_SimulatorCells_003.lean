module

public import PaperProofs.Paid.PDROC_SimulatorCells_002
public import PaperProofs.Paid.PDROC_Simulator_029
public import PaperProofs.Paid.PDROC_SimulatorReturns_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulator_cell_writing_observables (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (decision : Bool) (hd : record.decision = some decision)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance)))
    (hcell : sample ∈ P.recordCell fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) stage record B) :
    P.stageObservationBill fee hfee C accounting (simulatorRule P fee hfee source) stage sample =
      simulatorEndpointCharge P record (simulatorFreshEndpoint P fee hfee stage sample) ∧
    (P.actualWriteError fee hfee C accounting (simulatorRule P fee hfee source) stage sample ↔
      simulatorFreshEndpoint P fee hfee stage sample ∈ simulatorEndpointError P record) := by
  obtain ⟨entry, he, _, hr⟩ := hcell
  have hb := simulator_boundaryStage_pointwise P fee hfee C accounting source sample.1 sample.2 hfinite stage entry he
  change match ((simulatorData P fee hfee source).record sample.1 stage entry).decision with
    | none => _ | some decision => _ at hb
  rw [hr, hd] at hb
  obtain ⟨n, hn, hcount, hdecision⟩ := hb
  constructor
  · unfold PaperProofs.Paid.Parameters.stageObservationBill simulatorEndpointCharge
    change ENNReal.ofReal (P.reviewFee : ℝ) *
      (P.paidRunReviewCount fee hfee C .uncapped accounting (simulatorRule P fee hfee source) sample stage : ℝ≥0∞) =
      P.binarySymmetric.experiment.observationCharge
        ((P.binarySymmetric.rocEndpointTest record.level).rule.stop (sample.1.2.2 stage)
          (worldTapes (P.input fee hfee) sample.2 stage))
    rw [hn, hcount, PaperProofs.Statistics.BinaryExperiment.observationCharge_eq]
    rfl
  · change (_ = some (!((P.input fee hfee).truthAt sample.2 stage))) ↔ _
    rw [hdecision]
    simp only [Option.some.injEq]
    change (Bool.xor decision (Bool.xor record.orientation
      ((P.binarySymmetric.rocEndpointTest record.level).rule.decision (sample.1.2.2 stage)
        (worldTapes (P.input fee hfee) sample.2 stage))) = !((P.input fee hfee).truthAt sample.2 stage)) ↔
      flippedRecordDecision P record (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage) ≠
        ((P.input fee hfee).truthAt sample.2 stage)
    unfold flippedRecordDecision endpointCoordinateFlip
    rw [hd]
    simp only [Option.getD_some]
    cases htruth : (P.input fee hfee).truthAt sample.2 stage <;>
      cases hguess : recordEndpointGuess P record (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage) <;>
      cases decision <;> cases record.orientation <;> simp_all [recordEndpointGuess]

omit [MeasurableSpace Seed] in
theorem simulator_cell_virtualPosterior_iff (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ (stage : P.sharedInstance.Stage) (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (hreturns : ∃ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) sample = some history)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (decision : Bool) (hd : record.decision = some decision)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance)))
    (hcell : sample ∈ P.recordCell fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) stage record B) :
    (∃ history, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) sample = some history ∧
      (historyReport history stage).map Prod.fst = some (!record.orientation)) ↔
    simulatorFreshEndpoint P fee hfee stage sample ∈ simulatorEndpointPosterior P record := by
  obtain ⟨entry, he, _, hr⟩ := hcell
  exact simulator_virtualPosterior_event_iff P fee hfee C accounting source sample.1 sample.2 hfinite hreturns
    stage entry he record hr decision hd

theorem simulator_completedHistory_ae_returns (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure (SimulatorSeed P Seed)) [IsProbabilityMeasure ν] :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν, ∃ history,
      completedHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source.rule) sample = some history := by
  have hz := simulator_completedHistory_none_zero P fee hfee C accounting source ν
  have heq : {sample : SimulatorSeed P Seed × (P.input fee hfee).World |
      ¬ ∃ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source.rule) sample = some history} =
      {sample | completedHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source.rule) sample = none} := by
    ext sample
    cases hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) sample <;> simp [hh]
  apply ae_iff.mpr
  change (P.input fee hfee).seededWorldLaw ν {sample |
    ¬ ∃ history, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) sample = some history} = 0
  rw [heq]
  exact hz
end PDROC

