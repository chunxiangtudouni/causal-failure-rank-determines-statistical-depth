module

public import PaperProofs.Paid.PDMenu_ZeroChargeBill_145
public import PaperProofs.Paid.PDMenu_ZeroChargeActualRisk_147

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped BigOperators ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Only the source's explicit H0 qualification is assumed. Zero reviews
and zero full-path spending are proved from the actual blind script. -/
theorem zeroCharge_native (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (hqual : P.ZeroChargeOriginalQualification fee hfee C accounting) :
    ∃ policy : Policy (P.input fee hfee) C.val .native accounting (MenuSeed P.certificate.stages P.tools),
      policy.rule = P.zeroChargeRule fee ∧
      expectedBill (P.input fee hfee) C.val .native accounting policy.rule
        (menuSeedLaw P.certificate.stages P.tools) = 0 ∧
      risk (P.input fee hfee) C.val .native accounting policy.rule
        (menuSeedLaw P.certificate.stages P.tools) = ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) := by
  let source := P.zeroChargePolicy fee hfee C accounting
  have hr : ReviewQuotaCertificate (P.input fee hfee) C.val accounting source.rule (fun _ => 0) := by
    intro sample clock stage
    change (run (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample clock).ledger.reviews stage ≤ 0
    exact ((zeroCharge_run_free P fee hfee C accounting sample clock).2 stage).le
  have ht : C.val.normalCallBound + (∑ _ : P.sharedInstance.Stage, (0:ℕ)) +
      min P.sharedInstance.stageCount P.sharedInstance.toolCount ≤ C.val.totalCallCap := by
    simp only [Finset.sum_const_zero, add_zero, P.stageCount_eq]
    change C.val.normalCallBound + min P.certificate.stages P.tools ≤ C.val.totalCallCap
    have htotal := hqual.1.total_calls
    have hmin := min_le_right P.certificate.stages P.tools
    omega
  let native := source.enforceCaps (P.input fee hfee) C.val accounting (fun _ => 0) hr hqual.2
    (fun _ => Nat.zero_le _) ht
  refine ⟨native, rfl, ?_, ?_⟩
  · calc
      _ = expectedBill (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee)
          (menuSeedLaw P.certificate.stages P.tools) :=
        enforceCaps_expectedBill_eq (P.input fee hfee) C.val accounting source (fun _ => 0) hr hqual.2
          (fun _ => Nat.zero_le _) ht _
      _ = 0 := zeroCharge_expectedBill P fee hfee C accounting
  · calc
      _ = risk (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee)
          (menuSeedLaw P.certificate.stages P.tools) :=
        enforceCaps_risk_eq (P.input fee hfee) C.val accounting source (fun _ => 0) hr hqual.2
          (fun _ => Nat.zero_le _) ht _
      _ = _ := zeroCharge_risk P fee hfee C accounting

end PDMenu
