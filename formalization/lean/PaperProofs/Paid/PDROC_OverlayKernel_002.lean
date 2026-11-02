module

public import PaperProofs.Paid.PDROC_OverlayKernel_001
public import PaperProofs.Paid.PDROC_RecordCoupling_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid PaperProofs.Statistics.BinarySymmetric
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

noncomputable def overlayLocalMixtureWeight (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Set.Icc (0 : ℝ) 1 :=
  P.binarySymmetric.rocInitialWeight (P.overlayRecordTarget fee record)
    (P.overlayRecordTarget_pos fee hfee record) (P.overlayRecordTarget_le_half fee record)

noncomputable def overlayLocalMarkWeight (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Set.Icc (0 : ℝ) 1 :=
  ⟨PaperProofs.Paid.Parameters.falsePositiveProbability
      (P.recordDecisionError record) (P.overlayRecordTarget fee record),
    P.overlayRecord_falsePositive_mem_Icc fee hfee record⟩

noncomputable def overlayLocalActualLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) : Measure ((Bool × Bool) × P.experiment.Tape) :=
  P.binarySymmetric.experiment.conditionalLaw
    (adjacentMixtureSeedLaw (overlayLocalMixtureWeight P fee hfee record)) truth

instance overlayLocalActualLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    IsProbabilityMeasure (overlayLocalActualLaw P fee hfee record truth) := by
  unfold overlayLocalActualLaw
  exact PaperProofs.Statistics.BinaryExperiment.conditionalLaw_probability _ _ _

def overlayLocalErrorEvent (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) : Set ((Bool × Bool) × P.experiment.Tape) :=
  {sample | (P.overlayRecordTest fee hfee record).rule.decision sample.1 sample.2 ≠ truth}

theorem measurableSet_overlayLocalErrorEvent (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    MeasurableSet (overlayLocalErrorEvent P fee hfee record truth) :=
  ((P.overlayRecordTest fee hfee record).measurable_decision (measurableSet_singleton truth)).compl

/-- The actual prescribed adjacent MAP experiment has exactly p' error for
each hidden truth. This is proved by D05, not assumed of the policy. -/
theorem overlayLocal_actual_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    overlayLocalActualLaw P fee hfee record truth
      (overlayLocalErrorEvent P fee hfee record truth) =
        ENNReal.ofReal (P.overlayRecordTarget fee record) :=
  (adjacentMixtureAttains P.binarySymmetric (P.overlayRecordTarget fee record)
    (P.overlayRecordTarget_pos fee hfee record) (P.overlayRecordTarget_le_half fee record)).1 truth

noncomputable def overlayLocalExperimentLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    Measure (((Bool × Bool) × P.experiment.Tape) × Bool) :=
  (overlayLocalActualLaw P fee hfee record truth).prod
    (rocCoinLaw (overlayLocalMarkWeight P fee hfee record))

theorem overlayLocal_virtual_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    overlayLocalExperimentLaw P fee hfee record truth
      (overlayKernelVirtualEvent (overlayLocalErrorEvent P fee hfee record truth)) =
        ENNReal.ofReal (P.recordDecisionError record) := by
  exact overlayKernel_virtual_probability _ _
    (measurableSet_overlayLocalErrorEvent P fee hfee record truth)
    (P.overlayRecordTarget fee record) (P.recordDecisionError record)
    (P.overlayRecordTarget_pos fee hfee record).le
    (lt_of_le_of_lt (P.overlayRecordTarget_le_half fee record) (by norm_num))
    (P.overlayRecordTarget_le_decisionError fee record)
    (by have h := (P.recordDecisionError_bounds record).2
        linarith [P.recordPosteriorError_pos record])
    (overlayLocal_actual_probability P fee hfee record truth)

theorem overlayLocal_falsePositive_cell (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool)
    (B : Set ((Bool × Bool) × P.experiment.Tape)) :
    overlayLocalExperimentLaw P fee hfee record truth
        (((B ∩ (overlayLocalErrorEvent P fee hfee record truth)ᶜ) ×ˢ Set.univ) ∩
          overlayKernelVirtualEvent (overlayLocalErrorEvent P fee hfee record truth)) =
      ENNReal.ofReal (PaperProofs.Paid.Parameters.falsePositiveProbability
        (P.recordDecisionError record) (P.overlayRecordTarget fee record)) *
      overlayLocalExperimentLaw P fee hfee record truth
        ((B ∩ (overlayLocalErrorEvent P fee hfee record truth)ᶜ) ×ˢ Set.univ) :=
  overlayKernel_falsePositive_cell _ _ _ B

/-- Independent false-positive marks leave the entire all-path observation
charge unchanged, including the infinity value for a nonreturning test. -/
theorem overlayLocal_expectedCharge (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool) :
    (∫⁻ sample, P.experiment.observationCharge
        ((P.overlayRecordTest fee hfee record).rule.stop sample.1.1 sample.1.2)
      ∂overlayLocalExperimentLaw P fee hfee record truth) =
        P.binarySymmetric.rocPrice (P.overlayRecordTarget fee record) := by
  have hm : Measurable (fun sample : (((Bool × Bool) × P.experiment.Tape) × Bool) =>
      P.experiment.observationCharge
        ((P.overlayRecordTest fee hfee record).rule.stop sample.1.1 sample.1.2)) :=
    ((measurable_of_countable P.experiment.observationCharge).comp
      (P.overlayRecordTest fee hfee record).measurable_stop).comp measurable_fst
  rw [overlayLocalExperimentLaw, lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  exact (adjacentMixtureAttains P.binarySymmetric (P.overlayRecordTarget fee record)
    (P.overlayRecordTarget_pos fee hfee record) (P.overlayRecordTarget_le_half fee record)).2 truth

end PDROC
