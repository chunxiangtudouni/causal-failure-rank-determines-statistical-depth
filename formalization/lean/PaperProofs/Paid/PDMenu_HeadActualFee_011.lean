module

public import PaperProofs.Paid.PDMenu_CurrentPaymentPhases_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

/-- The real head correction is paid at the actual execute prefix, before
advance or any continuation. No future-success event appears in this identity. -/
theorem paidHeadThen_wrong_correctionBill {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head (some tool) good bad
    (run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 3)).ledger.correctionBill
      input.fees = ENNReal.ofReal (input.fees.correction head tool : ℝ) := by
  dsimp only
  rw [paidHeadThen_run_wrong_execute input C hC.1.1 hC.1.2 hC.2 accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong]
  have he := (bellmanHeadWrittenState_empty_corrections input C hC.1.1 accounting head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n
    (test.rule.decision sample.1 (worldTapes input sample.2 head))).2
  simp only [bellmanExecuteState, bellmanAllocateState, record, executeLedger, allocateLedger,
    Ledger.correctionBill, he, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- Even a later failed, abandoned or nonreturned whole task retains this
physically executed head fee in its true all-prefix actual-bill supremum. -/
theorem headCorrectionFee_le_fullBill {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head (some tool) good bad
    ENNReal.ofReal (input.fees.correction head tool : ℝ) ≤
      runActualBill input C .uncapped accounting (paidHeadThenRule input head test available after) sample := by
  dsimp only
  rw [← paidHeadThen_wrong_correctionBill input C hC accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong]
  exact (le_add_left (le_refl _) : _ ≤ (run input C .uncapped accounting
    (paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad)) sample (n + 3)).ledger.actualBill input.fees).trans
      (prefixBill_le_runActualBill input C .uncapped accounting _ sample (n + 3))

end PDMenu
