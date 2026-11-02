module

public import PaperProofs.Paid.PDROC_FirstFailure_006
public import PaperProofs.Paid.PDROC_Termination_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

theorem firstFailurePolicy_expectedBill_le (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting
      (firstFailurePolicy P fee hfee C mode accounting source).rule ν ≤
      expectedBill (P.input fee hfee) C.val mode accounting source.rule ν :=
  lintegral_mono (fun sample => (firstFailurePolicy_domination P fee hfee C mode accounting source).2.2.2 sample |>.2)

theorem firstFailurePolicy_risk_eq (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    risk (P.input fee hfee) C.val .uncapped accounting
      (firstFailurePolicy P fee hfee C mode accounting source).rule ν =
      risk (P.input fee hfee) C.val mode accounting source.rule ν := by
  unfold risk
  congr 1
  ext sample
  exact not_congr ((firstFailurePolicy_domination P fee hfee C mode accounting source).1 sample)

/-- The complete first normalization step of original D06, for every original
finite-full-bill policy and seed universe. This is not the later boundary or
virtual-history representation. All failure fees and infinite penalties remain. -/
theorem finiteCost_firstFailureNormalization (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed)
    (hf : expectedBill (P.input fee hfee) C.val mode accounting source.rule ν ≠ ⊤) :
    ∃ stopped : Policy (P.input fee hfee) C.val .uncapped accounting Seed,
      FirstFailureDomination (P.input fee hfee) C.val mode accounting source stopped ∧
      expectedBill (P.input fee hfee) C.val .uncapped accounting stopped.rule ν ≤
        expectedBill (P.input fee hfee) C.val mode accounting source.rule ν ∧
      (P.input fee hfee).seededWorldLaw ν {sample |
        completedHistory (P.input fee hfee) C.val .uncapped accounting stopped.rule sample = none} = 0 ∧
      ∀ penalty : ℝ≥0∞,
        paidPenaltyObjective (P.input fee hfee) C.val accounting stopped.rule ν penalty ≤
          expectedBill (P.input fee hfee) C.val mode accounting source.rule ν +
            penalty * risk (P.input fee hfee) C.val mode accounting source.rule ν := by
  let stopped := firstFailurePolicy P fee hfee C mode accounting source
  have hbill := firstFailurePolicy_expectedBill_le P fee hfee C mode accounting source ν
  refine ⟨stopped, firstFailurePolicy_domination P fee hfee C mode accounting source, hbill, ?_, ?_⟩
  · exact paid_finiteExpectedBill_completedHistory P fee hfee C.val .uncapped accounting stopped ν
      (ne_top_of_le_ne_top hf hbill)
  · intro penalty
    unfold paidPenaltyObjective
    rw [firstFailurePolicy_risk_eq]
    exact add_le_add hbill le_rfl

end PDROC
