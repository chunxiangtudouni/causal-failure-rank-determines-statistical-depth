module

public import PaperProofs.Paid.PA17_D31Witness_001
public import PaperProofs.Paid.PA17_D31Witness_Law_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.PA17D31WitnessCost005

open Common Common.Native PA17D31Witness001

theorem ledger_correctionBill_const (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (L : Ledger P.sharedInstance) :
    L.correctionBill (P.input fee hfee).fees =
      ENNReal.ofReal (fee : ℝ) * (L.executions.length : ℝ≥0∞) := by
  simp [Ledger.correctionBill, Parameters.actual_correctionFee,
    List.sum_replicate, nsmul_eq_mul, mul_comm]

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Actual physical payments on every path, including failure. -/
theorem runActualBill_eq_fee_mul_repairs (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C mode accounting Seed)
    (hnoreview : ∀ seed history stage, policy.rule seed history ≠ .review stage)
    (sample : Seed × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C mode accounting policy.rule sample =
      ENNReal.ofReal (fee : ℝ) * runRepairCount (P.input fee hfee) C mode accounting policy.rule sample := by
  unfold runActualBill runRepairCount
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  rw [Ledger.actualBill, ledger_correctionBill_const]
  simp [Ledger.observationBill, run_reviews_zero (P.input fee hfee) C mode accounting policy hnoreview]

theorem expectedBill_eq_fee_mul_expectedRepairs (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C mode accounting Seed)
    (hnoreview : ∀ seed history stage, policy.rule seed history ≠ .review stage) (ν : Measure Seed) :
    expectedBill (P.input fee hfee) C mode accounting policy.rule ν =
      ENNReal.ofReal (fee : ℝ) * expectedRepairCount (P.input fee hfee) C mode accounting policy.rule ν := by
  unfold expectedBill expectedRepairCount
  simp_rw [runActualBill_eq_fee_mul_repairs P fee hfee C mode accounting policy hnoreview]
  exact lintegral_const_mul _ (measurable_runRepairCount (P.input fee hfee) C mode accounting
    policy.rule policy.measurable_rule)

/-- Pointwise genuine execution counts feed directly into the original
expected-repair field. The assignment-event mass comes from DLower. -/
theorem expectedRepairCount_of_pathCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C mode accounting Unit)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 2)
    (hmass : (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = ENNReal.ofReal delta)
    (hcount : ∀ sample : Unit × (P.input fee hfee).World,
      runRepairCount (P.input fee hfee) C mode accounting policy.rule sample =
        if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
        else (P.blindErrorCount fee hfee sample : ℝ≥0∞)) :
    expectedRepairCount (P.input fee hfee) C mode accounting policy.rule (Measure.dirac ()) =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 - P.certificate.stages * delta) := by
  have hfun : runRepairCount (P.input fee hfee) C mode accounting policy.rule =
      PA17D31WitnessLaw004.truncatedErrorCount P fee hfee := by
    funext sample
    exact hcount sample
  rw [expectedRepairCount, hfun]
  exact PA17D31WitnessLaw004.lintegral_truncatedErrorCount P fee hfee delta hdelta hsmall hmass

theorem expectedRepairCount_original (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hfee) C mode accounting Unit)
    (hdelta : P.certificate.risk = (1 / 2 : ℚ) ^ P.certificate.stages)
    (hcount : ∀ sample : Unit × (P.input fee hfee).World,
      runRepairCount (P.input fee hfee) C mode accounting policy.rule sample =
        if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
        else (P.blindErrorCount fee hfee sample : ℝ≥0∞)) :
    expectedRepairCount (P.input fee hfee) C mode accounting policy.rule (Measure.dirac ()) =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 -
        P.certificate.stages * (P.certificate.risk : ℝ)) := by
  have hd : 0 ≤ (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos.le
  have hs : (P.certificate.risk : ℝ) ≤ 1 / 2 := by
    have hsmall : (P.certificate.risk : ℝ) ≤ ((1 / 64 : ℚ) : ℝ) := Rat.cast_le.mpr P.certificate.risk_le
    norm_num at hsmall
    linarith
  exact expectedRepairCount_of_pathCount P fee hfee C mode accounting policy
    (P.certificate.risk : ℝ) hd hs
    (PA17D31WitnessLaw004.original_full_error_mass P fee hfee hdelta) hcount

end PaperProofs.Paid.PA17D31WitnessCost005
