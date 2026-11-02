module

public import PaperProofs.Paid.PDROC_OverlayCells_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

theorem overlayEndpointLaw_actual_correct (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    overlayEndpointLaw P fee hfee stage ((overlayEndpointActualError P fee hfee record)ᶜ) =
      ENNReal.ofReal (1 - P.overlayRecordTarget fee record) := by
  rw [measure_compl (measurableSet_overlayEndpointActualError P fee hfee record)
    (measure_ne_top _ _), measure_univ, overlayEndpointLaw_actual_error]
  rw [ENNReal.ofReal_sub 1 (P.overlayRecordTarget_pos fee hfee record).le]
  norm_num

theorem overlayEndpointLaw_false_positive_amount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    overlayEndpointLaw P fee hfee stage
        ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record) =
      ENNReal.ofReal (PaperProofs.Paid.Parameters.falsePositiveProbability
        (P.recordDecisionError record) (P.overlayRecordTarget fee record)) *
          ENNReal.ofReal (1 - P.overlayRecordTarget fee record) := by
  apply overlayEndpointLaw_measure_of_conditional_constant P fee hfee stage _
    ((measurableSet_overlayEndpointActualError P fee hfee record).compl.inter
      (measurableSet_overlayEndpointVirtualError P fee hfee record))
  intro truth
  let A := overlayLocalErrorEvent P fee hfee record truth
  have hA : MeasurableSet A := measurableSet_overlayLocalErrorEvent P fee hfee record truth
  have hlocalSet : MeasurableSet ((Aᶜ ×ˢ (Set.univ : Set Bool)) ∩ overlayKernelVirtualEvent A) :=
    (hA.compl.prod MeasurableSet.univ).inter (measurableSet_overlayKernelVirtualEvent A hA)
  have heq : ((fun pair : OverlayStageCoins × P.experiment.Tape => (pair.1, (truth, pair.2))) ⁻¹'
      ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record)) =
      (overlayRowExperimentSample P record) ⁻¹'
        ((Aᶜ ×ˢ (Set.univ : Set Bool)) ∩ overlayKernelVirtualEvent A) := by
    ext pair
    simp only [Set.mem_preimage, overlayEndpointVirtualError, overlayEndpointActualError,
      overlayRowExperimentSample, overlayKernelVirtualEvent, A, overlayLocalErrorEvent,
      Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ,
      Set.mem_compl_iff, Set.mem_singleton_iff, and_true]
    tauto
  rw [heq, ← Measure.map_apply (measurable_overlayRowExperimentSample P record) hlocalSet,
    overlayRowConditionalLaw_experiment]
  have hc : overlayLocalActualLaw P fee hfee record truth Aᶜ =
      ENNReal.ofReal (1 - P.overlayRecordTarget fee record) := by
    rw [measure_compl hA (measure_ne_top _ _), measure_univ]
    rw [show overlayLocalActualLaw P fee hfee record truth A =
      ENNReal.ofReal (P.overlayRecordTarget fee record) from overlayLocal_actual_probability P fee hfee record truth]
    rw [ENNReal.ofReal_sub 1 (P.overlayRecordTarget_pos fee hfee record).le]
    norm_num
  calc
    _ = ENNReal.ofReal (PaperProofs.Paid.Parameters.falsePositiveProbability
        (P.recordDecisionError record) (P.overlayRecordTarget fee record)) *
          overlayLocalExperimentLaw P fee hfee record truth (Aᶜ ×ˢ Set.univ) := by
      simpa only [Set.univ_inter] using overlayLocal_falsePositive_cell P fee hfee record truth Set.univ
    _ = _ := by rw [overlayLocalExperimentLaw, Measure.prod_prod, measure_univ, mul_one, hc]

theorem overlayEndpointLaw_false_positive (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    overlayEndpointLaw P fee hfee stage
        ((overlayEndpointActualError P fee hfee record)ᶜ ∩ overlayEndpointVirtualError P fee hfee record) =
      ENNReal.ofReal (PaperProofs.Paid.Parameters.falsePositiveProbability
        (P.recordDecisionError record) (P.overlayRecordTarget fee record)) *
          overlayEndpointLaw P fee hfee stage (overlayEndpointActualError P fee hfee record)ᶜ := by
  rw [overlayEndpointLaw_false_positive_amount, overlayEndpointLaw_actual_correct]

end PDROC
