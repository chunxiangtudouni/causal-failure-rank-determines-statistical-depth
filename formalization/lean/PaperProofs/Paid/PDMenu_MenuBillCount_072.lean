module

public import PaperProofs.Paid.PDMenu_CurrentReplayFees_025
public import PaperProofs.Paid.PDROC_MarkedFees_001
public import PaperProofs.Common.NativeRepairCount

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

/-- Exact all-path full bill for a constant actual execution fee. Both
suprema include failed, abandoned, and nonreturning paths. -/
theorem constantFee_runActualBill_eq (input : StatisticalInput I) (fee : ℚ)
    (hfee : ∀ stage tool, input.fees.correction stage tool = fee)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) :
    runActualBill input C mode accounting rule sample =
      runObservationBill input C mode accounting rule sample +
        ENNReal.ofReal (fee : ℝ) * runRepairCount input C mode accounting rule sample := by
  have ho : Monotone (fun n => (run input C mode accounting rule sample n).ledger.observationBill input.fees) := by
    intro n m hnm
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C mode accounting rule hlegal sample stage hnm)) _
  have hc : Monotone (fun n => (run input C mode accounting rule sample n).ledger.correctionBill input.fees) := by
    intro n m hnm
    dsimp only
    rw [correctionBill_constant input.fees fee hfee, correctionBill_constant input.fees fee hfee]
    apply mul_le_mul' _ le_rfl
    exact_mod_cast PDROC.run_executionCount_mono input C mode accounting rule sample hnm
  calc
    _ = (⨆ n, (run input C mode accounting rule sample n).ledger.observationBill input.fees) +
        ⨆ n, (run input C mode accounting rule sample n).ledger.correctionBill input.fees :=
      (ENNReal.iSup_add_iSup_of_monotone ho hc).symm
    _ = _ := by
      simp_rw [correctionBill_constant input.fees fee hfee]
      rw [← ENNReal.iSup_mul, mul_comm]
      rfl

variable [MeasurableSpace Seed]

/-- The original expected full bill is exactly observation spending plus
the actual execution count mean, without finite-expectation assumptions. -/
theorem constantFee_expectedBill_eq (input : StatisticalInput I) (fee : ℚ)
    (hfee : ∀ stage tool, input.fees.correction stage tool = fee)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    expectedBill input C mode accounting policy.rule ν =
      expectedObservationBill input C mode accounting policy.rule ν +
        ENNReal.ofReal (fee : ℝ) * expectedRepairCount input C mode accounting policy.rule ν := by
  unfold expectedBill expectedObservationBill expectedRepairCount
  simp_rw [constantFee_runActualBill_eq input fee hfee C mode accounting policy.rule policy.legal]
  rw [lintegral_add_left (measurable_runObservationBill input C mode accounting policy.rule policy.measurable_rule),
    lintegral_const_mul _ (measurable_runRepairCount input C mode accounting policy.rule policy.measurable_rule)]

end PDMenu
