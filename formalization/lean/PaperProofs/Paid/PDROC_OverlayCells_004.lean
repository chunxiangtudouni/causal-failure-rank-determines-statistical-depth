module

public import PaperProofs.Paid.PDROC_OverlayCells_001
public import PaperProofs.Paid.PDROC_OverlayCells_003
public import PaperProofs.Paid.PDROC_SimulatorCells_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Local actual observables follow solely from the ORIGINAL D14 stage
realization, before any source-history or fee comparison is available. -/
theorem overlay_cell_writing_observables_of_stage (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (OverlaySeed P Seed))
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν
      (overlayRule P fee hfee source) (overlayData P source))
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (decision : Bool)
    (hd : record.decision = some decision) (B : Set (Seed × List (VisibleEvent P.sharedInstance))) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      sample ∈ P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
        (overlayData P source).toRecordSimulatorData stage record B →
      P.stageObservationBill fee hfee C accounting (overlayRule P fee hfee source) stage sample =
        overlayEndpointCharge P fee hfee record (overlayFreshCurrent P fee hfee stage sample) ∧
      (P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ↔
        overlayFreshCurrent P fee hfee stage sample ∈ overlayEndpointActualError P fee hfee record) := by
  filter_upwards [hstage] with sample hs
  intro hc
  obtain ⟨entry, he, _, hr⟩ := hc
  have hb := hs stage entry he
  dsimp only at hb
  rw [hr, hd] at hb
  obtain ⟨n, hn, hcount, hdecision, _⟩ := hb
  let tape : P.binarySymmetric.experiment.Tape := (P.input fee hfee).reviewAt sample.2 stage
  let coins : Bool × Bool := (overlayData P source).mixtureCoinsAtRecord sample.1 stage record
  have hstop : (P.overlayRecordTest fee hfee record).rule.stop coins tape = (n : ℕ∞) := hn
  have hdec : P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) sample stage =
      some ((P.overlayRecordTest fee hfee record).rule.decision coins tape) := hdecision
  constructor
  · unfold PaperProofs.Paid.Parameters.stageObservationBill overlayEndpointCharge
    change ENNReal.ofReal (P.reviewFee : ℝ) *
      (P.paidRunReviewCount fee hfee C .uncapped accounting (overlayRule P fee hfee source) sample stage : ℝ≥0∞) =
        P.binarySymmetric.experiment.observationCharge ((P.overlayRecordTest fee hfee record).rule.stop coins tape)
    rw [hstop, hcount, PaperProofs.Statistics.BinaryExperiment.observationCharge_eq]
    rfl
  · change (_ = some (!((P.input fee hfee).truthAt sample.2 stage))) ↔ _
    rw [hdec]
    simp only [Option.some.injEq]
    change ((P.overlayRecordTest fee hfee record).rule.decision coins tape = !(sample.2 stage).1) ↔
      (P.overlayRecordTest fee hfee record).rule.decision coins tape ≠ (sample.2 stage).1
    cases (P.overlayRecordTest fee hfee record).rule.decision coins tape <;> cases (sample.2 stage).1 <;> decide

/-- Actual error and all-path observation charge on each original measurable
old-seed/full-entry writing cell, assuming only the original stage proposition. -/
theorem overlayActualRecordCells_of_stage (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting
      (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
      (overlayRule P fee hfee source) (overlayData P source))
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (decision : Bool)
    (hd : record.decision = some decision)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) (hB : MeasurableSet B) :
    let μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
    let cell := P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData stage record B
    MeasurableSet cell ∧
      μ (cell ∩ {sample | P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample}) =
        ENNReal.ofReal (P.overlayRecordTarget fee record) * μ cell ∧
      (∫⁻ sample, cell.indicator (P.stageObservationBill fee hfee C accounting (overlayRule P fee hfee source) stage) sample ∂μ) =
        P.binarySymmetric.rocPrice (P.overlayRecordTarget fee record) * μ cell := by
  dsimp only
  let μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
  let gate := overlayRecordGate P fee hfee C accounting source stage
  let ρ := μ.map gate
  let ε := overlayEndpointLaw P fee hfee stage
  let joint := fun sample : OverlaySeed P Seed × (P.input fee hfee).World =>
    (gate sample, overlayFreshCurrent P fee hfee stage sample)
  let D := overlayRecordCellGateSet P record B
  let cell := P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
    (overlayData P source).toRecordSimulatorData stage record B
  have hg : Measurable gate := measurable_overlayRecordGate P fee hfee C accounting source hm stage
  have hj : Measurable joint := hg.prodMk (by unfold overlayFreshCurrent; fun_prop)
  have hlaw : μ.map joint = ρ.prod ε :=
    overlayRecordGate_joint_actualMarginal P fee hfee C accounting source hm ν
      (overlayPaidStageCoinsLaw P fee hfee) stage ((fun _ => (false, false)), fun _ => false)
  have hD : MeasurableSet D := measurableSet_overlayRecordCellGateSet P record B hB
  have hcell : cell = joint ⁻¹' (D ×ˢ Set.univ) := by
    rw [show cell = gate ⁻¹' D from overlay_recordCell_eq_gate_preimage P fee hfee C accounting source stage record decision hd B]
    ext sample
    simp [joint]
  let : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ε := overlayEndpointLaw_probability P fee hfee stage
  have hobs := overlay_cell_writing_observables_of_stage P fee hfee C accounting source
    (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee)) hstage stage record decision hd B
  have hcost : ∀ᵐ sample ∂μ, sample ∈ cell →
      P.stageObservationBill fee hfee C accounting (overlayRule P fee hfee source) stage sample =
        overlayEndpointCharge P fee hfee record (joint sample).2 := by
    filter_upwards [hobs] with sample hs
    exact fun hc => (hs hc).1
  have herror : ∀ᵐ sample ∂μ, sample ∈ cell →
      (P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ↔
        (joint sample).2 ∈ overlayEndpointActualError P fee hfee record) := by
    filter_upwards [hobs] with sample hs
    exact fun hc => (hs hc).2
  refine ⟨measurableSet_overlay_recordCell P fee hfee C accounting source hm stage record decision hd B hB, ?_, ?_⟩
  · have h := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
      (P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage)
      (overlayEndpointActualError P fee hfee record) (measurableSet_overlayEndpointActualError P fee hfee record) herror
    rw [overlayEndpointLaw_actual_error] at h
    exact h
  · have h := productGate_cell_lintegral μ ρ ε joint hj hlaw D hD cell hcell
      (P.stageObservationBill fee hfee C accounting (overlayRule P fee hfee source) stage)
      (overlayEndpointCharge P fee hfee record) (measurable_overlayEndpointCharge P fee hfee record) hcost
    rw [overlayEndpointLaw_charge] at h
    exact h

end PDROC
