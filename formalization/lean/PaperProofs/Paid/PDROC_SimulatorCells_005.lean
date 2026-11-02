module

public import PaperProofs.Paid.PDROC_SimulatorCells_003
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

/-- The ORIGINAL BoundaryRecordCells for the actual concrete Native simulator.
The generated gate retains the old seed and full virtual entry and record,
while the real endpoint coin and truth/tape stay an independent product. -/
theorem simulatorBoundaryRecordCells (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    P.BoundaryRecordCells fee hfee C accounting (simulatorSeedLaw P ν)
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule) := by
  intro stage record decision hd B hB
  let μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)
  let ρ := simulatorRecordGateLaw P fee hfee C accounting source.rule ν stage
  let ε := simulatorEndpointLaw P fee hfee stage
  let joint := fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
    (simulatorGeneratedRecordGate P fee hfee C accounting source.rule stage sample,
      simulatorFreshEndpoint P fee hfee stage sample)
  let D := simulatorRecordGateCell P record B
  let cell := P.recordCell fee hfee C accounting (simulatorRule P fee hfee source.rule)
    (simulatorData P fee hfee source.rule) stage record B
  have hj : Measurable joint := by
    apply Measurable.prodMk
    · exact measurable_simulatorGeneratedRecordGate P fee hfee C accounting source.rule source.measurable_rule stage
    · unfold simulatorFreshEndpoint
      fun_prop
  have hlaw : μ.map joint = ρ.prod ε :=
    simulatorGeneratedRecordGate_jointLaw P fee hfee C accounting source.rule source.measurable_rule ν stage
  have hD : MeasurableSet D := measurableSet_simulatorRecordGateCell P record B hB
  have hcell : cell = joint ⁻¹' (D ×ˢ Set.univ) := by
    change P.recordCell fee hfee C accounting (simulatorRule P fee hfee source.rule)
      (simulatorData P fee hfee source.rule) stage record B = _
    rw [simulator_recordCell_eq_gate_preimage]
    ext sample
    simp [joint, D]
  let : IsProbabilityMeasure ρ := by
    unfold ρ simulatorRecordGateLaw
    apply (Measure.isProbabilityMeasure_map_iff
      (measurable_simulatorRecordGateFactor P fee hfee C accounting source.rule source.measurable_rule stage).aemeasurable).2
    exact @Measure.prod.instIsProbabilityMeasure _ P.experiment.Tape _ _ _ _
      (simulatorAllOtherLaw_probability P fee hfee ν stage) (auxiliaryTapeLaw_probability P)
  let : IsProbabilityMeasure ε := simulatorEndpointLaw_probability P fee hfee stage
  have hcost : ∀ᵐ sample ∂μ, sample ∈ cell →
      P.stageObservationBill fee hfee C accounting (simulatorRule P fee hfee source.rule) stage sample =
        simulatorEndpointCharge P record (joint sample).2 := by
    filter_upwards [allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)] with sample hs
    intro hc
    exact (simulator_cell_writing_observables P fee hfee C accounting source.rule sample hs
      stage record decision hd B hc).1
  have herror : ∀ᵐ sample ∂μ, sample ∈ cell →
      (P.actualWriteError fee hfee C accounting (simulatorRule P fee hfee source.rule) stage sample ↔
        (joint sample).2 ∈ simulatorEndpointError P record) := by
    filter_upwards [allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)] with sample hs
    intro hc
    exact (simulator_cell_writing_observables P fee hfee C accounting source.rule sample hs
      stage record decision hd B hc).2
  have hposterior : ∀ᵐ sample ∂μ, sample ∈ cell →
      ((∃ history, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample = some history ∧
        (historyReport history stage).map Prod.fst = some (!record.orientation)) ↔
          (joint sample).2 ∈ simulatorEndpointPosterior P record) := by
    filter_upwards [allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν),
      simulator_completedHistory_ae_returns P fee hfee C accounting source (simulatorSeedLaw P ν)] with sample hs hr
    intro hc
    exact simulator_cell_virtualPosterior_iff P fee hfee C accounting source.rule sample hs hr
      stage record decision hd B hc
  change MeasurableSet cell ∧ _ ∧ _ ∧ _
  refine ⟨hcell ▸ (hD.prod MeasurableSet.univ).preimage hj, ?_, ?_, ?_⟩
  · have h := productGate_cell_lintegral μ ρ ε joint hj hlaw D hD cell hcell
      (P.stageObservationBill fee hfee C accounting (simulatorRule P fee hfee source.rule) stage)
      (simulatorEndpointCharge P record) (measurable_simulatorEndpointCharge P record) hcost
    rw [simulatorEndpointLaw_charge] at h
    exact h
  · have h := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
      (P.actualWriteError fee hfee C accounting (simulatorRule P fee hfee source.rule) stage)
      (simulatorEndpointError P record) (measurableSet_simulatorEndpointError P record) herror
    rw [simulatorEndpointLaw_error] at h
    exact h
  · have h := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
      (fun sample => ∃ history, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample = some history ∧
        (historyReport history stage).map Prod.fst = some (!record.orientation))
      (simulatorEndpointPosterior P record) (measurableSet_simulatorEndpointPosterior P record) hposterior
    rw [simulatorEndpointLaw_posterior] at h
    exact h

end PDROC


