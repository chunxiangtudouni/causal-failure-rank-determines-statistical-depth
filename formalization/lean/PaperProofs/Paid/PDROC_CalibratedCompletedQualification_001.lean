module

public import PaperProofs.Paid.PDROC_CalibratedResources_003
public import PaperProofs.Common.BoundedNormalIO

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedCompletedQualification

theorem zeroChargeRule_ne_review (P : Parameters) (fee : ℚ)
    (seed : MenuSeed P.certificate.stages P.tools)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) :
    P.zeroChargeRule fee seed history ≠ .review stage := by
  intro selected
  unfold Parameters.zeroChargeRule searchGuardRule at selected
  dsimp only at selected
  split at selected
  · exact PDROC.CalibratedResources.zeroChargeCandidateRule_ne_review P fee seed history stage selected
  · cases selected

/-- The original zero-charge script requests no review on any actual
prefix. This uses only its literal visible action rule. -/
theorem zeroChargeRule_reviewQuotaCertificate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    ReviewQuotaCertificate (P.input fee hfee) C.val accounting (P.zeroChargeRule fee) (fun _ => 0) := by
  intro sample clock stage
  obtain ⟨_, _, path⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
    (P.zeroChargeRule fee) (P.zeroChargePolicy fee hfee C accounting).legal sample clock
  apply prefix_reviews_le_of_review_gate (P.input fee hfee) C.val .uncapped accounting
    (P.zeroChargeRule fee) sample.1 ((P.input fee hfee).truthAt sample.2)
    (worldTapes (P.input fee hfee) sample.2) (fun _ => 0) _ path stage
  intro _earlierClock state _earlier _active reviewed selected
  exact (zeroChargeRule_ne_review P fee sample.1 state.history reviewed selected).elim

theorem zeroChargeRule_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World) :
    (run (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample
      (quotaActionBound P.sharedInstance (fun _ => 0) + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate (P.input fee hfee) C.val accounting (P.zeroChargeRule fee)
    (P.zeroChargePolicy fee hfee C accounting).legal (fun _ => 0)
    (zeroChargeRule_reviewQuotaCertificate P fee hfee C accounting) sample

/-- The SAME arbitrary H0 bounds completed actual calibrated executions
iff it bounds all actual prefixes. Every halted failure is included. -/
theorem calibrated_normalCalls_iff_completed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (H0 : ℕ) :
    NormalCallCertificate (P.input fee hfee) C.val .uncapped accounting
        (P.calibratedAlgorithmPolicy fee hfee C accounting) H0 ↔
      CompletedNormalCallBound (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) H0 :=
  normalCallCertificate_iff_completed_of_halts (P.input fee hfee) C.val .uncapped accounting
    (P.calibratedAlgorithmPolicy fee hfee C accounting) H0
    (fun sample => ⟨_, PDROC.CalibratedResources.calibratedAlgorithm_halted P fee hfee C accounting sample⟩)

theorem zeroCharge_normalCalls_iff_completed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (H0 : ℕ) :
    NormalCallCertificate (P.input fee hfee) C.val .uncapped accounting
        (P.zeroChargePolicy fee hfee C accounting) H0 ↔
      CompletedNormalCallBound (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) H0 :=
  normalCallCertificate_iff_completed_of_halts (P.input fee hfee) C.val .uncapped accounting
    (P.zeroChargePolicy fee hfee C accounting) H0
    (fun sample => ⟨_, zeroChargeRule_halted P fee hfee C accounting sample⟩)

/-- No qualification arithmetic is changed: this is exactly the original
THIS-script qualification, expressed with complete-run normal-I/O H0. -/
theorem calibratedOriginalQualification_iff_completed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.CalibratedOriginalQualification fee hfee C accounting ↔
      P.NativeCapQualification C ∧
        CompletedNormalCallBound (P.input fee hfee) C.val .uncapped accounting
          (P.calibratedAlgorithmRule fee) C.val.normalCallBound := by
  constructor
  · rintro ⟨caps, prefixes⟩
    exact ⟨caps, (calibrated_normalCalls_iff_completed P fee hfee C accounting C.val.normalCallBound).mp prefixes⟩
  · rintro ⟨caps, completed⟩
    exact ⟨caps, (calibrated_normalCalls_iff_completed P fee hfee C accounting C.val.normalCallBound).mpr completed⟩

theorem zeroChargeOriginalQualification_iff_completed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.ZeroChargeOriginalQualification fee hfee C accounting ↔
      P.NativeCapQualification C ∧
        CompletedNormalCallBound (P.input fee hfee) C.val .uncapped accounting
          (P.zeroChargeRule fee) C.val.normalCallBound := by
  constructor
  · rintro ⟨caps, prefixes⟩
    exact ⟨caps, (zeroCharge_normalCalls_iff_completed P fee hfee C accounting C.val.normalCallBound).mp prefixes⟩
  · rintro ⟨caps, completed⟩
    exact ⟨caps, (zeroCharge_normalCalls_iff_completed P fee hfee C accounting C.val.normalCallBound).mpr completed⟩

end PDROC.CalibratedCompletedQualification
