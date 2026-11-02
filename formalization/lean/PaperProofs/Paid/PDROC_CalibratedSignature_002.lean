module

public import PaperProofs.Paid.PDROC_CalibratedSignature_001
public import PaperProofs.Paid.PDMenu_MenuBillCount_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.CalibratedSignature

variable {Seed : Type*}

/-- Decode the original uniform physical-execution fee from the full
signature. A committed but never executed tool contributes nothing. -/
noncomputable def signatureCorrectionBill (P : Parameters) (fee : ℚ)
    (signature : P.ExecutionSignature) : ℝ≥0∞ := by
  classical
  exact ((Finset.univ.filter (fun tool : P.sharedInstance.Tool =>
    ∃ stage : P.sharedInstance.Stage, signature.2.2.1 stage tool = true)).card : ℝ≥0∞) *
      ENNReal.ofReal (fee : ℝ)

theorem measurable_signatureCorrectionBill (P : Parameters) (fee : ℚ) :
    Measurable (signatureCorrectionBill P fee) := measurable_of_countable _

theorem everExecutedTools_eq_signature (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) :
    everExecutedTools (P.input fee hfee) C.val mode accounting rule sample =
      Finset.univ.filter (fun tool : P.sharedInstance.Tool =>
        ∃ stage : P.sharedInstance.Stage,
          (P.executionSignature fee hfee C mode accounting rule sample).2.2.1 stage tool = true) := by
  classical
  ext tool
  rw [mem_everExecutedTools]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨clock, member⟩
    obtain ⟨execution, present, sameTool⟩ :=
      (show ∃ execution ∈ (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.executions,
        execution.tool = tool by
        simpa only [ledgerExecutedTools, List.mem_toFinset, List.mem_map] using member)
    refine ⟨execution.handle.stage, ?_⟩
    change decide (∃ clock, ∃ e ∈ (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.executions,
      e.handle.stage = execution.handle.stage ∧ e.tool = tool) = true
    exact decide_eq_true ⟨clock, execution, present, rfl, sameTool⟩
  · rintro ⟨stage, written⟩
    change decide (∃ clock, ∃ execution ∈
      (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.executions,
        execution.handle.stage = stage ∧ execution.tool = tool) = true at written
    obtain ⟨clock, execution, present, _sameStage, sameTool⟩ := of_decide_eq_true written
    refine ⟨clock, ?_⟩
    simp only [ledgerExecutedTools, List.mem_toFinset, List.mem_map]
    exact ⟨execution, present, sameTool⟩

theorem runActualCorrectionBill_eq_count (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) :
    P.runActualCorrectionBill fee hfee C mode accounting rule sample =
      runRepairCount (P.input fee hfee) C.val mode accounting rule sample * ENNReal.ofReal (fee : ℝ) := by
  unfold Parameters.runActualCorrectionBill runRepairCount
  simp_rw [PDROC.paid_correctionBill_eq_count]
  rw [ENNReal.iSup_mul]

/-- Exact supremum correction bill, retaining executions paid before
failure, abandonment, or nonreturn. No eventual-return hypothesis. -/
theorem runActualCorrectionBill_eq_signature (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed)
    (legal : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) :
    P.runActualCorrectionBill fee hfee C mode accounting rule sample =
      signatureCorrectionBill P fee (P.executionSignature fee hfee C mode accounting rule sample) := by
  rw [runActualCorrectionBill_eq_count,
    runRepairCount_eq_everExecutedTools_card (P.input fee hfee) C.val mode accounting rule legal sample,
    everExecutedTools_eq_signature]
  rfl

theorem runActualBill_eq_observation_add_correction (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed)
    (legal : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val mode accounting rule sample =
      runObservationBill (P.input fee hfee) C.val mode accounting rule sample +
        P.runActualCorrectionBill fee hfee C mode accounting rule sample := by
  rw [PDMenu.constantFee_runActualBill_eq (P.input fee hfee) fee (fun _ _ => rfl) C.val mode accounting rule legal sample,
    runActualCorrectionBill_eq_count, mul_comm (runRepairCount (P.input fee hfee) C.val mode accounting rule sample)]

section Measurable

variable [MeasurableSpace Seed]

theorem expectedBill_eq_observation_add_correction (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν =
      expectedObservationBill (P.input fee hfee) C.val mode accounting policy.rule ν +
        P.expectedActualCorrectionBill fee hfee C mode accounting policy.rule ν := by
  unfold expectedBill expectedObservationBill Parameters.expectedActualCorrectionBill
  simp_rw [runActualBill_eq_observation_add_correction P fee hfee C mode accounting policy.rule policy.legal]
  exact lintegral_add_left
    (measurable_runObservationBill (P.input fee hfee) C.val mode accounting policy.rule policy.measurable_rule) _

theorem actualCorrectionBillLaw_eq_signature_map (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    P.actualCorrectionBillLaw fee hfee C mode accounting policy.rule ν =
      (P.executionSignatureLaw fee hfee C mode accounting policy.rule ν).map (signatureCorrectionBill P fee) := by
  unfold Parameters.actualCorrectionBillLaw Parameters.executionSignatureLaw
  rw [Measure.map_map (measurable_signatureCorrectionBill P fee)
    (P.measurable_executionSignature fee hfee C mode accounting policy.rule policy.measurable_rule)]
  apply Measure.map_congr
  exact ae_of_all _ (runActualCorrectionBill_eq_signature P fee hfee C mode accounting policy.rule policy.legal)

theorem risk_eq_signature_failure_mass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    risk (P.input fee hfee) C.val mode accounting policy.rule ν =
      P.executionSignatureLaw fee hfee C mode accounting policy.rule ν
        {signature | signature.2.2.2 = true} := by
  classical
  have measurable : MeasurableSet {signature : P.ExecutionSignature | signature.2.2.2 = true} :=
    (measurable_of_countable (fun signature : P.ExecutionSignature => signature.2.2.2))
      (measurableSet_singleton true)
  unfold risk Parameters.executionSignatureLaw
  rw [Measure.map_apply
    (P.measurable_executionSignature fee hfee C mode accounting policy.rule policy.measurable_rule) measurable]
  congr 1
  ext sample
  simp only [Parameters.executionSignature, Set.mem_preimage, Set.mem_ofPred_eq, decide_eq_true_eq]

end Measurable

section Comparison

variable {SourceSeed TargetSeed : Type*} [MeasurableSpace SourceSeed] [MeasurableSpace TargetSeed]

theorem risk_eq_of_signatureLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (actual : Policy (P.input fee hfee) C.val mode accounting TargetSeed) (νactual : Measure TargetSeed)
    (source : Policy (P.input fee hfee) C.val mode accounting SourceSeed) (νsource : Measure SourceSeed)
    (same : P.executionSignatureLaw fee hfee C mode accounting actual.rule νactual =
      P.executionSignatureLaw fee hfee C mode accounting source.rule νsource) :
    risk (P.input fee hfee) C.val mode accounting actual.rule νactual =
      risk (P.input fee hfee) C.val mode accounting source.rule νsource := by
  rw [risk_eq_signature_failure_mass P fee hfee C mode accounting actual νactual,
    risk_eq_signature_failure_mass P fee hfee C mode accounting source νsource, same]

theorem correctionBillLaw_eq_of_signatureLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (actual : Policy (P.input fee hfee) C.val mode accounting TargetSeed) (νactual : Measure TargetSeed)
    (source : Policy (P.input fee hfee) C.val mode accounting SourceSeed) (νsource : Measure SourceSeed)
    (same : P.executionSignatureLaw fee hfee C mode accounting actual.rule νactual =
      P.executionSignatureLaw fee hfee C mode accounting source.rule νsource) :
    P.actualCorrectionBillLaw fee hfee C mode accounting actual.rule νactual =
      P.actualCorrectionBillLaw fee hfee C mode accounting source.rule νsource := by
  rw [actualCorrectionBillLaw_eq_signature_map P fee hfee C mode accounting actual νactual,
    actualCorrectionBillLaw_eq_signature_map P fee hfee C mode accounting source νsource, same]

theorem expectedCorrectionBill_eq_of_signatureLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (actual : Policy (P.input fee hfee) C.val mode accounting TargetSeed) (νactual : Measure TargetSeed)
    (source : Policy (P.input fee hfee) C.val mode accounting SourceSeed) (νsource : Measure SourceSeed)
    (same : P.executionSignatureLaw fee hfee C mode accounting actual.rule νactual =
      P.executionSignatureLaw fee hfee C mode accounting source.rule νsource) :
    P.expectedActualCorrectionBill fee hfee C mode accounting actual.rule νactual =
      P.expectedActualCorrectionBill fee hfee C mode accounting source.rule νsource := by
  have laws := correctionBillLaw_eq_of_signatureLaw P fee hfee C mode accounting actual νactual source νsource same
  have means := congrArg (fun law : Measure ℝ≥0∞ => ∫⁻ bill, bill ∂law) laws
  simp only [Parameters.actualCorrectionBillLaw] at means
  rw [lintegral_map (f := fun bill : ℝ≥0∞ => bill) measurable_id
      (P.measurable_runActualCorrectionBill fee hfee C mode accounting actual.rule actual.measurable_rule),
    lintegral_map (f := fun bill : ℝ≥0∞ => bill) measurable_id
      (P.measurable_runActualCorrectionBill fee hfee C mode accounting source.rule source.measurable_rule)] at means
  exact means

end Comparison

end PDROC.CalibratedSignature
