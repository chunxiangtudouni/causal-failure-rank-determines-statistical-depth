module

public import PaperProofs.Common.NativePricing
public import PaperProofs.Paid.Model

/-!
The four Appendix-D values use one and the same current-payment protocol.
Changing f transports every full randomized history policy without changing
its path or risk. Only actual execution charges change; caps never increase.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Paid.Parameters

open Common

variable {Seed : Type*} [MeasurableSpace Seed]

theorem input_reprice_eq (P : PaperProofs.Paid.Parameters) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) :
    (P.input oldFee hold).withCorrectionFee (fun _ _ => fee) (fun _ _ => hfee) = P.input fee hfee := rfl

def repricePolicy (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract) (mode : Native.ResourceMode)
    (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee)
    (policy : Native.Policy (P.input oldFee hold) C.val mode accounting Seed) :
    Native.Policy (P.input fee hfee) C.val mode accounting Seed :=
  policy.reprice (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee) C.val mode accounting

omit [MeasurableSpace Seed] in
theorem legalRule_same_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract) (mode : Native.ResourceMode)
    (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (rule : PolicyRule P.sharedInstance Seed) :
    Native.LegalRule (P.input oldFee hold) C.val mode accounting rule ↔
      Native.LegalRule (P.input fee hfee) C.val mode accounting rule :=
  Native.legalRule_reprice_iff (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee)
    C.val mode accounting rule

omit [MeasurableSpace Seed] in
theorem run_same_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract) (mode : Native.ResourceMode)
    (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (rule : PolicyRule P.sharedInstance Seed)
    (sample : Seed × (P.input oldFee hold).World) (n : ℕ) :
    Native.run (P.input fee hfee) C.val mode accounting rule sample n =
      Native.run (P.input oldFee hold) C.val mode accounting rule sample n :=
  Native.run_reprice_eq (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee) C.val mode accounting rule sample n

theorem risk_same_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract) (mode : Native.ResourceMode)
    (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) :
    Native.risk (P.input fee hfee) C.val mode accounting rule ν =
      Native.risk (P.input oldFee hold) C.val mode accounting rule ν :=
  Native.risk_reprice_eq (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee) C.val mode accounting rule ν

theorem expectedObservationBill_same_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) :
    Native.expectedObservationBill (P.input fee hfee) C.val mode accounting rule ν =
      Native.expectedObservationBill (P.input oldFee hold) C.val mode accounting rule ν :=
  Native.expectedObservationBill_reprice_eq (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee)
    C.val mode accounting rule ν

theorem expectedBill_mono_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance) (oldFee fee : ℚ)
    (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (hmono : oldFee ≤ fee)
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) :
    Native.expectedBill (P.input oldFee hold) C.val mode accounting rule ν ≤
      Native.expectedBill (P.input fee hfee) C.val mode accounting rule ν :=
  Native.expectedBill_mono_reprice (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee)
    (fun _ _ => hmono) C.val mode accounting rule ν

theorem free_ledger_actualBill (P : PaperProofs.Paid.Parameters) (L : Ledger P.sharedInstance) :
    L.actualBill (P.input 0 (by norm_num)).fees = L.observationBill (P.input 0 (by norm_num)).fees := by
  simp [Ledger.actualBill, Ledger.correctionBill, StatisticalInput.fees, input]

omit [MeasurableSpace Seed] in
theorem free_runActualBill_eq_observation (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input 0 (by norm_num)).World) :
    Native.runActualBill (P.input 0 (by norm_num)) C.val mode accounting rule sample =
      Native.runObservationBill (P.input 0 (by norm_num)) C.val mode accounting rule sample := by
  apply iSup_congr
  intro n
  exact P.free_ledger_actualBill _

theorem free_expectedBill_eq_observation (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) :
    Native.expectedBill (P.input 0 (by norm_num)) C.val mode accounting rule ν =
      Native.expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting rule ν := by
  exact lintegral_congr (P.free_runActualBill_eq_observation C mode accounting rule)

end PaperProofs.Paid.Parameters

namespace PaperProofs.Paid.Parameters

open Common

theorem paidValue_mono_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (oldFee fee : ℚ) (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (hmono : oldFee ≤ fee) :
    P.paidValue C mode accounting oldFee hold ≤ P.paidValue C mode accounting fee hfee :=
  Native.value_mono_reprice (P.input oldFee hold) (fun _ _ => fee) (fun _ _ => hfee)
    (fun _ _ => hmono) C.val mode accounting (ENNReal.ofReal (P.certificate.risk : ℝ))

theorem nativeValue_mono_fee (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance)
    (oldFee fee : ℚ) (hold : 0 ≤ oldFee) (hfee : 0 ≤ fee) (hmono : oldFee ≤ fee) :
    P.nativeValue C accounting oldFee hold ≤ P.nativeValue C accounting fee hfee :=
  P.paidValue_mono_fee C .native accounting oldFee fee hold hfee hmono

theorem freeValue_le_paidValue (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    P.freeValue C mode accounting ≤ P.paidValue C mode accounting fee hfee :=
  P.paidValue_mono_fee C mode accounting 0 fee (by norm_num) hfee hfee

end PaperProofs.Paid.Parameters
