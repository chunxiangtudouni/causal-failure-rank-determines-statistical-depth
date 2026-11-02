module

public import PaperProofs.Paid.PDROC_OverlayCells_002
public import PaperProofs.Paid.PDROC_OverlayCells_004
public import PaperProofs.Paid.PDROC_OverlaySimulator_022
public import PaperProofs.Paid.PDLower_Allowance_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem overlay_measurableSet_actualWriteError (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    MeasurableSet {sample : OverlaySeed P Seed × (P.input fee hfee).World |
      P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample} := by
  let : MeasurableSpace (Option Bool) := ⊤
  let : MeasurableSingletonClass (Option Bool) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact measurableSet_eq_fun
    (PDLower.measurable_actualOrdinaryDecision P fee hfee C .uncapped accounting
      (overlayRule P fee hfee source) (measurable_overlayRule P fee hfee source hm) stage)
    ((measurable_of_countable (fun truth : Bool => some (!truth))).comp
      (((measurable_pi_apply stage).comp measurable_snd).fst))

theorem overlay_cell_virtual_observables_of_stage_path (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (OverlaySeed P Seed))
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν
      (overlayRule P fee hfee source) (overlayData P source))
    (hpath : OverlayDraft.OverlayPathCoupling P fee hfee C accounting
      (overlayRule P fee hfee source) (overlayData P source))
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (decision : Bool)
    (hd : record.decision = some decision) (B : Set (Seed × List (VisibleEvent P.sharedInstance))) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      sample ∈ P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
        (overlayData P source).toRecordSimulatorData stage record B →
      (P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
        (overlayData P source).toRecordSimulatorData stage sample ↔
        overlayFreshCurrent P fee hfee stage sample ∈ overlayEndpointVirtualError P fee hfee record) := by
  have hobs := overlay_cell_writing_observables_of_stage P fee hfee C accounting source ν hstage
    stage record decision hd B
  filter_upwards [hstage, hobs] with sample hs ho
  intro hc
  have hactual := (ho hc).2
  obtain ⟨entry, he, _, hr⟩ := hc
  have hb := hs stage entry he
  dsimp only at hb
  rw [hr, hd] at hb
  obtain ⟨n, _, _, hdecision, _⟩ := hb
  have hreport := overlay_actualOrdinaryDecision_report_exists P fee hfee C .uncapped accounting
    (overlayRule P fee hfee source) (overlayRule_legal P fee hfee C accounting source) sample stage _ hdecision
  have hor := hpath.2.2.1 sample stage entry decision he (by rw [hr]; exact hd) hreport
  rw [hr] at hor
  rw [hor, hactual]
  rfl

/-- Complete ORIGINAL record-cell contents, with only the explicit original
Stage/Path conclusions left as inputs. All probability gates are on old seed,
FULL virtual entry and source record; no source-law or finite-ET is assumed. -/
theorem overlayRecordCells_of_stage_path (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting
      (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
      (overlayRule P fee hfee source) (overlayData P source))
    (hpath : OverlayDraft.OverlayPathCoupling P fee hfee C accounting
      (overlayRule P fee hfee source) (overlayData P source)) :
    OverlayDraft.OverlayRecordCells P fee hfee C accounting
      (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
      (overlayRule P fee hfee source) (overlayData P source) := by
  intro stage record decision hd B hB
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
  let : IsProbabilityMeasure ε := overlayEndpointLaw_probability P fee hfee stage
  have hac := overlayActualRecordCells_of_stage P fee hfee C accounting source hm ν hstage stage record decision hd B hB
  have hobs := overlay_cell_writing_observables_of_stage P fee hfee C accounting source
    (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee)) hstage stage record decision hd B
  have he : ∀ᵐ sample ∂μ, sample ∈ cell →
      (P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ↔
        (joint sample).2 ∈ overlayEndpointActualError P fee hfee record) := by
    filter_upwards [hobs] with sample hs
    exact fun hc => (hs hc).2
  have hv := overlay_cell_virtual_observables_of_stage_path P fee hfee C accounting source
    (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee)) hstage hpath stage record decision hd B
  have hvirtual : ∀ᵐ sample ∂μ, sample ∈ cell →
      (P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
        (overlayData P source).toRecordSimulatorData stage sample ↔
        (joint sample).2 ∈ overlayEndpointVirtualError P fee hfee record) := hv
  have hec : ∀ᵐ sample ∂μ, sample ∈ cell →
      (¬P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ↔
        (joint sample).2 ∈ (overlayEndpointActualError P fee hfee record)ᶜ) := by
    filter_upwards [he] with sample hs
    exact fun hc => not_congr (hs hc)
  have hfp : ∀ᵐ sample ∂μ, sample ∈ cell →
      ((¬P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ∧
        P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
          (overlayData P source).toRecordSimulatorData stage sample) ↔
        (joint sample).2 ∈ ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record)) := by
    filter_upwards [hec, hvirtual] with sample hs ht
    intro hc
    exact and_congr (hs hc) (ht hc)
  have hVmass := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
    (fun sample => P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData stage sample)
    (overlayEndpointVirtualError P fee hfee record) (measurableSet_overlayEndpointVirtualError P fee hfee record) hvirtual
  rw [overlayEndpointLaw_virtual_error] at hVmass
  have hECmass := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
    (fun sample => ¬P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample)
    (overlayEndpointActualError P fee hfee record)ᶜ (measurableSet_overlayEndpointActualError P fee hfee record).compl hec
  have hFPmass := productGate_cell_event μ ρ ε joint hj hlaw D hD cell hcell
    (fun sample => ¬P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ∧
      P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
        (overlayData P source).toRecordSimulatorData stage sample)
    ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record)
    ((measurableSet_overlayEndpointActualError P fee hfee record).compl.inter
      (measurableSet_overlayEndpointVirtualError P fee hfee record)) hfp
  change MeasurableSet cell ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hac.1, overlay_measurableSet_actualWriteError P fee hfee C accounting source hm stage,
    overlay_measurableSet_virtualWriteError P fee hfee C accounting (overlayRule P fee hfee source)
      (measurable_overlayRule P fee hfee source hm) (overlayData P source).toRecordSimulatorData
      (overlayData_measurable P source hm).1 stage, hac.2.1, hVmass, ?_, hac.2.2⟩
  calc
    _ = μ (cell ∩ {sample | ¬P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ∧
        P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source)
          (overlayData P source).toRecordSimulatorData stage sample}) := by
      congr 1
      ext sample
      simp only [cell, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, and_assoc]
    _ = ε ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record) * μ cell := hFPmass
    _ = ENNReal.ofReal (PaperProofs.Paid.Parameters.falsePositiveProbability
        (P.recordDecisionError record) (P.overlayRecordTarget fee record)) *
        (ε (overlayEndpointActualError P fee hfee record)ᶜ * μ cell) := by
      rw [overlayEndpointLaw_false_positive, mul_assoc]
    _ = _ := by
      rw [← hECmass]
      rfl

/-- StageRealization is already proved for this actual controller. Thus the
only remaining input to this cell component is the explicit original Path target. -/
theorem overlayRecordCells_of_path (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hpath : OverlayDraft.OverlayPathCoupling P fee hfee C accounting
      (overlayRule P fee hfee source) (overlayData P source)) :
    OverlayDraft.OverlayRecordCells P fee hfee C accounting
      (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))
      (overlayRule P fee hfee source) (overlayData P source) :=
  overlayRecordCells_of_stage_path P fee hfee C accounting source hm ν
    (overlayStageRealization P fee hfee C accounting source
      (overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee))) hpath

end PDROC
