module

public import PaperProofs.Paid.PDROC_MarkedFees_001
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u
variable {Seed : Type u}

theorem observationBill_run_mono (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) :
    Monotone (fun n => (run (P.input fee hf) C.val mode accounting rule sample n).ledger.observationBill (P.input fee hf).fees) := by
  intro n m hnm
  apply Finset.sum_le_sum
  intro stage _
  exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono (P.input fee hf) C.val mode accounting rule hl sample stage hnm)) _

theorem runObservation_add_correctionCount_le (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) :
    runObservationBill (P.input fee hf) C.val mode accounting rule sample +
      ENNReal.ofReal (fee : ℝ) * runRepairCount (P.input fee hf) C.val mode accounting rule sample ≤
      runActualBill (P.input fee hf) C.val mode accounting rule sample := by
  rw [runObservationBill, runRepairCount, ENNReal.mul_iSup, ENNReal.iSup_add]
  apply iSup_le
  intro n
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro m
  have hob := observationBill_run_mono P fee hf C mode accounting rule hl sample (Nat.le_max_left n m)
  have hr := PDROC.run_executionCount_mono (P.input fee hf) C.val mode accounting rule sample (Nat.le_max_right n m)
  have hrepair : ENNReal.ofReal (fee : ℝ) * ((run (P.input fee hf) C.val mode accounting rule sample m).ledger.executions.length : ℝ≥0∞) ≤
      ENNReal.ofReal (fee : ℝ) * ((run (P.input fee hf) C.val mode accounting rule sample (max n m)).ledger.executions.length : ℝ≥0∞) := by
    exact mul_le_mul' le_rfl (by exact_mod_cast hr)
  calc
    _ ≤ (run (P.input fee hf) C.val mode accounting rule sample (max n m)).ledger.observationBill (P.input fee hf).fees +
        ENNReal.ofReal (fee : ℝ) * ((run (P.input fee hf) C.val mode accounting rule sample (max n m)).ledger.executions.length : ℝ≥0∞) :=
      add_le_add hob hrepair
    _ = (run (P.input fee hf) C.val mode accounting rule sample (max n m)).ledger.actualBill (P.input fee hf).fees := by
      rw [Ledger.actualBill, PDROC.paid_correctionBill_eq_count, mul_comm]
    _ ≤ _ := le_iSup (fun n => (run (P.input fee hf) C.val mode accounting rule sample n).ledger.actualBill (P.input fee hf).fees) (max n m)

variable [MeasurableSpace Seed]

theorem expectedObservation_add_correctionCount_le (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hf) C.val mode accounting Seed) (ν : Measure Seed) :
    expectedObservationBill (P.input fee hf) C.val mode accounting policy.rule ν +
      ENNReal.ofReal (fee : ℝ) * expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν ≤
      expectedBill (P.input fee hf) C.val mode accounting policy.rule ν := by
  unfold expectedObservationBill expectedRepairCount expectedBill
  rw [← lintegral_const_mul _ (measurable_runRepairCount (P.input fee hf) C.val mode accounting policy.rule policy.measurable_rule),
    ← lintegral_add_left (measurable_runObservationBill (P.input fee hf) C.val mode accounting policy.rule policy.measurable_rule)]
  exact lintegral_mono (runObservation_add_correctionCount_le P fee hf C mode accounting policy.rule policy.legal)

end PDLower
