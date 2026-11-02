module

public import PaperProofs.Paid.PDROC_CalibratedResources_002
public import PaperProofs.Common.BoundedNormalIO

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedResources

theorem guarded_reviewQuotaCertificate {Seed : Type*} (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (candidate : PolicyRule P.sharedInstance Seed)
    (gate : ∀ seed history stage, candidate seed history = .review stage →
      (historyObservations history stage).length < P.certificate.Q) :
    ReviewQuotaCertificate (P.input fee hfee) C.val accounting (searchGuardRule candidate)
      (fun _ => P.certificate.Q) := by
  intro sample clock stage
  have legal := searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting candidate
  obtain ⟨_, _, path⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
    (searchGuardRule candidate) legal sample clock
  apply prefix_reviews_le_of_review_gate (P.input fee hfee) C.val .uncapped accounting
    (searchGuardRule candidate) sample.1 ((P.input fee hfee).truthAt sample.2)
    (worldTapes (P.input fee hfee) sample.2) (fun _ => P.certificate.Q) _ path stage
  intro earlierClock state earlier _active reviewed selected
  have raw : candidate sample.1 state.history = .review reviewed := by
    unfold searchGuardRule at selected
    dsimp only at selected
    split at selected
    · exact selected
    · cases selected
  have bound := gate sample.1 state.history reviewed raw
  rw [← prefix_historyObservations_length (P.input fee hfee) C.val .uncapped accounting
    (searchGuardRule candidate) sample.1 ((P.input fee hfee).truthAt sample.2)
    (worldTapes (P.input fee hfee) sample.2) earlier reviewed]
  exact ENat.natCast_lt_natCast.mpr bound

theorem calibratedTable_reviewQuotaCertificate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (table : MenuTable) :
    ReviewQuotaCertificate (P.input fee hfee) C.val accounting
      (searchGuardRule (P.calibratedMenuCandidate table)) (fun _ => P.certificate.Q) :=
  guarded_reviewQuotaCertificate P fee hfee C accounting (P.calibratedMenuCandidate table)
    (fun seed history stage selected => calibratedMenuCandidate_review_lt P table seed history stage selected)

theorem calibratedState_reviewQuotaCertificate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (state : MultiplierState) :
    ReviewQuotaCertificate (P.input fee hfee) C.val accounting (P.calibratedStateRule state)
      (fun _ => P.certificate.Q) :=
  guarded_reviewQuotaCertificate P fee hfee C accounting (P.calibratedStateCandidate state)
    (fun seed history stage selected => calibratedStateCandidate_review_lt P state seed history stage selected)

theorem calibratedTable_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (table : MenuTable)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    (run (P.input fee hfee) C.val .uncapped accounting (searchGuardRule (P.calibratedMenuCandidate table))
      sample (quotaActionBound P.sharedInstance (fun _ => P.certificate.Q) + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate (P.input fee hfee) C.val accounting
    (searchGuardRule (P.calibratedMenuCandidate table))
    (searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting (P.calibratedMenuCandidate table))
    (fun _ => P.certificate.Q) (calibratedTable_reviewQuotaCertificate P fee hfee C accounting table) sample

theorem calibratedState_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (state : MultiplierState)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state)
      sample (quotaActionBound P.sharedInstance (fun _ => P.certificate.Q) + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate (P.input fee hfee) C.val accounting (P.calibratedStateRule state)
    (P.calibratedStatePolicy state fee hfee C accounting).legal
    (fun _ => P.certificate.Q) (calibratedState_reviewQuotaCertificate P fee hfee C accounting state) sample

theorem calibratedAlgorithm_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee)
      sample (quotaActionBound P.sharedInstance (fun _ => P.certificate.Q) + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate (P.input fee hfee) C.val accounting (P.calibratedAlgorithmRule fee)
    (P.calibratedAlgorithmPolicy fee hfee C accounting).legal (fun _ => P.certificate.Q)
    (calibratedAlgorithm_reviewQuotaCertificate P fee hfee C accounting) sample

end PDROC.CalibratedResources
