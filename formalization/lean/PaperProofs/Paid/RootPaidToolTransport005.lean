module

public import PaperProofs.Paid.RootPaidToolTransport004

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

theorem expectedBill_upPolicy_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedBill (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule ν =
      expectedBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) policy.rule ν := by
  unfold expectedBill
  rw [← (measurePreserving_upSample P fee hfee n k ν).lintegral_comp
    (measurable_runActualBill _ _ _ _ _ (upPolicy P fee hfee n k policy).val.measurable_rule)]
  exact lintegral_congr (runActualBill_upPolicy P fee hfee n k policy)

theorem risk_upPolicy_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    risk (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule ν ≤
      risk (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) policy.rule ν := by
  let bad : Set (Seed × (P.freshInput n (k + 1) fee hfee).World) := {sample |
    ¬ runSuccess (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule sample}
  have hm : MeasurableSet bad :=
    (measurableSet_runSuccess (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
      (zeroAccounting _) (upPolicy P fee hfee n k policy).val.rule
      (upPolicy P fee hfee n k policy).val.measurable_rule).compl
  have he : (P.freshInput n (k + 1) fee hfee).seededWorldLaw ν bad =
      (P.freshInput n k fee hfee).seededWorldLaw ν (upSample P fee hfee n k ⁻¹' bad) :=
    (congrArg (fun law : Measure (Seed × (P.freshInput n (k + 1) fee hfee).World) => law bad)
      (measurePreserving_upSample P fee hfee n k ν).map_eq).symm.trans
        (Measure.map_apply (measurePreserving_upSample P fee hfee n k ν).measurable hm)
  apply he.le.trans
  apply measure_mono
  intro sample hfailure hsuccess
  exact hfailure (runSuccess_upPolicy P fee hfee n k policy sample hsuccess)

theorem paidPenaltyObjective_upPolicy_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    paidPenaltyObjective (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule ν penalty ≤
      paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) policy.rule ν penalty := by
  unfold paidPenaltyObjective
  rw [expectedBill_upPolicy_eq]
  apply add_le_add le_rfl
  simpa only [mul_comm] using mul_le_mul_right (risk_upPolicy_le P fee hfee n k policy ν) penalty

theorem freshPaidPenalty_tools_antitone (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee n (k + 1) penalty ≤ P.freshPaidPenalty fee hfee n k penalty := by
  change paidPenaltyValue (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty ≤
    paidPenaltyValue (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty
  conv_rhs => unfold paidPenaltyValue
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact (paidPenaltyValue_le_policy _ _ _ penalty ν (upPolicy P fee hfee n k policy).val).trans
    (paidPenaltyObjective_upPolicy_le P fee hfee n k policy ν penalty)

end RootPaidToolTransport
