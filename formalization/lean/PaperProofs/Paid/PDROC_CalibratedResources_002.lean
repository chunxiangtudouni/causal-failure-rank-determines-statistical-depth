module

public import PaperProofs.Paid.PDROC_CalibratedResources_001
public import PaperProofs.Common.ReferenceTermination
public import PaperProofs.Common.NativeCapTransfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid MeasureTheory
open scoped BigOperators ENNReal

namespace PDROC.CalibratedResources

theorem prefix_calibratedAlgorithm_reviews_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (seed : P.CalibratedSearchSeed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {state : State P.sharedInstance}
    (path : Prefix (P.input fee hfee) C mode accounting (P.calibratedAlgorithmRule fee)
      seed truth tapes n state) :
    ∀ stage : P.sharedInstance.Stage, state.ledger.reviews stage ≤ (P.certificate.Q : ℕ∞) := by
  apply prefix_reviews_le_of_review_gate (P.input fee hfee) C mode accounting
    (P.calibratedAlgorithmRule fee) seed truth tapes (fun _ => P.certificate.Q) _ path
  intro clock current earlier _active stage selected
  have bound := calibratedAlgorithmRule_review_lt P fee seed current.history stage selected
  rw [← prefix_historyObservations_length (P.input fee hfee) C mode accounting
    (P.calibratedAlgorithmRule fee) seed truth tapes earlier stage]
  exact ENat.natCast_lt_natCast.mpr bound

theorem calibratedAlgorithm_reviewQuotaCertificate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    ReviewQuotaCertificate (P.input fee hfee) C.val accounting (P.calibratedAlgorithmRule fee)
      (fun _ => P.certificate.Q) := by
  intro sample clock stage
  obtain ⟨_, _, path⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
    (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmPolicy fee hfee C accounting).legal sample clock
  exact prefix_calibratedAlgorithm_reviews_le P fee hfee C.val .uncapped accounting
    sample.1 ((P.input fee hfee).truthAt sample.2) (worldTapes (P.input fee hfee) sample.2) path stage

theorem stage_card (P : Parameters) : Fintype.card P.sharedInstance.Stage = P.certificate.stages :=
  (Fintype.card_fin _).trans P.stageCount_eq

theorem sum_quota (P : Parameters) :
    (∑ _stage : P.sharedInstance.Stage, P.certificate.Q) = P.certificate.stages * P.certificate.Q := by
  simp only [Finset.sum_const, Finset.card_univ, stage_card, smul_eq_mul]

/-- Exact original first resource conjunction; all actual prefixes and
samples are covered, without success, risk, expected-cost or H0 premises. -/
theorem calibratedAlgorithm_resources (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    ∀ (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (n : ℕ),
      (∀ i, (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee)
        sample n).ledger.reviews i ≤ (P.certificate.Q : ℕ∞)) ∧
      (∑ i, (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee)
        sample n).ledger.reviews i) ≤ (P.certificate.stages * P.certificate.Q : ℕ) ∧
      (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee)
        sample n).ledger.executions.length ≤ P.tools := by
  intro sample n
  have reviews := calibratedAlgorithm_reviewQuotaCertificate P fee hfee C accounting sample n
  refine ⟨reviews, ?_, ?_⟩
  · calc
      _ ≤ ∑ _i : P.sharedInstance.Stage, (P.certificate.Q : ℕ∞) :=
        Finset.sum_le_sum (fun i _ => reviews i)
      _ = ((P.certificate.stages * P.certificate.Q : ℕ) : ℕ∞) := by
        simp only [Finset.sum_const, Finset.card_univ, stage_card, nsmul_eq_mul, Nat.cast_mul]
  · have bound := run_actualCorrections_le (P.input fee hfee) C.val .uncapped accounting
      (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmPolicy fee hfee C accounting).legal sample n
    exact bound.trans (min_le_right _ _)

theorem originalQualification_total (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting) :
    C.val.normalCallBound + (∑ _stage : P.sharedInstance.Stage, P.certificate.Q) +
      min P.sharedInstance.stageCount P.sharedInstance.toolCount ≤ C.val.totalCallCap := by
  rw [sum_quota]
  exact (Nat.add_le_add_left (min_le_right P.sharedInstance.stageCount P.sharedInstance.toolCount)
    (C.val.normalCallBound + P.certificate.stages * P.certificate.Q)).trans qualified.1.total_calls

/-- The same original fixed calibrated script. Only THIS script's original
NormalCallCertificate and arithmetic cap qualification are consumed. -/
def nativePolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting) :
    Policy (P.input fee hfee) C.val .native accounting P.CalibratedSearchSeed :=
  (P.calibratedAlgorithmPolicy fee hfee C accounting).enforceCaps (P.input fee hfee) C.val accounting
    (fun _ => P.certificate.Q) (calibratedAlgorithm_reviewQuotaCertificate P fee hfee C accounting)
    qualified.2 qualified.1.stage_quota (originalQualification_total P fee hfee C accounting qualified)

theorem nativePolicy_rule (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting) :
    (nativePolicy P fee hfee C accounting qualified).rule = P.calibratedAlgorithmRule fee := rfl

theorem nativePolicy_run_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (n : ℕ) :
    run (P.input fee hfee) C.val .native accounting (nativePolicy P fee hfee C accounting qualified).rule sample n =
      run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n :=
  (run_uncapped_eq_native (P.input fee hfee) C.val accounting (P.calibratedAlgorithmRule fee)
    (nativePolicy P fee hfee C accounting qualified).legal sample n).symm

theorem nativePolicy_risk_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting)
    (ν : Measure P.CalibratedSearchSeed) :
    risk (P.input fee hfee) C.val .native accounting (nativePolicy P fee hfee C accounting qualified).rule ν =
      risk (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) ν :=
  (risk_uncapped_eq_native (P.input fee hfee) C.val accounting (P.calibratedAlgorithmRule fee)
    (nativePolicy P fee hfee C accounting qualified).legal ν).symm

theorem nativePolicy_expectedBill_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting)
    (ν : Measure P.CalibratedSearchSeed) :
    expectedBill (P.input fee hfee) C.val .native accounting
      (nativePolicy P fee hfee C accounting qualified).rule ν =
        expectedBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) ν :=
  (expectedBill_uncapped_eq_native (P.input fee hfee) C.val accounting (P.calibratedAlgorithmRule fee)
    (nativePolicy P fee hfee C accounting qualified).legal ν).symm

theorem calibratedAlgorithm_nativeImplementation (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (qualified : P.CalibratedOriginalQualification fee hfee C accounting) :
    ∃ policy : Policy (P.input fee hfee) C.val .native accounting P.CalibratedSearchSeed,
      policy.rule = P.calibratedAlgorithmRule fee ∧
      (∀ sample n, run (P.input fee hfee) C.val .native accounting policy.rule sample n =
        run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n) ∧
      (∀ ν : Measure P.CalibratedSearchSeed,
        risk (P.input fee hfee) C.val .native accounting policy.rule ν =
          risk (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) ν) ∧
      (∀ ν : Measure P.CalibratedSearchSeed,
        expectedBill (P.input fee hfee) C.val .native accounting policy.rule ν =
          expectedBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) ν) :=
  ⟨nativePolicy P fee hfee C accounting qualified, rfl,
    nativePolicy_run_eq P fee hfee C accounting qualified,
    nativePolicy_risk_eq P fee hfee C accounting qualified,
    nativePolicy_expectedBill_eq P fee hfee C accounting qualified⟩

end PDROC.CalibratedResources
