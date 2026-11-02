module

public import PaperProofs.Paid.RootPaidToolTransport007

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

theorem runActualBill_downPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed)
    (sample : Seed × (P.freshInput n (k + 1) fee hfee).World) :
    runActualBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule (downSample P fee hfee n k sample) =
      runActualBill (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.val.rule sample := by
  unfold runActualBill
  apply iSup_congr
  intro time
  rw [run_downPolicy]
  exact (upLedger_actualBill P fee hfee n k _).symm

theorem runSuccess_downPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed)
    (sample : Seed × (P.freshInput n (k + 1) fee hfee).World)
    (h : runSuccess (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
      (zeroAccounting _) policy.val.rule sample) :
    runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule (downSample P fee hfee n k sample) := by
  obtain ⟨time, hh, hs⟩ := h
  rw [run_downPolicy] at hh hs
  exact ⟨time, hh, upLedger_success_reverse n k _ hs⟩

theorem expectedBill_downPolicy_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule ν =
      expectedBill (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.val.rule ν := by
  unfold expectedBill
  rw [← (measurePreserving_downSample P fee hfee n k ν).lintegral_comp
    (measurable_runActualBill _ _ _ _ _ (downPolicy P fee hfee n k policy).measurable_rule)]
  exact lintegral_congr (runActualBill_downPolicy P fee hfee n k policy)

theorem risk_downPolicy_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    risk (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule ν ≤
      risk (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.val.rule ν := by
  let bad : Set (Seed × (P.freshInput n k fee hfee).World) := {sample |
    ¬ runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule sample}
  have hm : MeasurableSet bad :=
    (measurableSet_runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
      (zeroAccounting _) (downPolicy P fee hfee n k policy).rule
      (downPolicy P fee hfee n k policy).measurable_rule).compl
  have he : (P.freshInput n k fee hfee).seededWorldLaw ν bad =
      (P.freshInput n (k + 1) fee hfee).seededWorldLaw ν (downSample P fee hfee n k ⁻¹' bad) :=
    (congrArg (fun law : Measure (Seed × (P.freshInput n k fee hfee).World) => law bad)
      (measurePreserving_downSample P fee hfee n k ν).map_eq).symm.trans
        (Measure.map_apply (measurePreserving_downSample P fee hfee n k ν).measurable hm)
  apply he.le.trans
  apply measure_mono
  intro sample hfailure hsuccess
  exact hfailure (runSuccess_downPolicy P fee hfee n k policy sample hsuccess)

theorem paidPenaltyObjective_downPolicy_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule ν penalty ≤
      paidPenaltyObjective (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
        (zeroAccounting _) policy.val.rule ν penalty := by
  unfold paidPenaltyObjective
  rw [expectedBill_downPolicy_eq]
  apply add_le_add le_rfl
  simpa only [mul_comm] using mul_le_mul_right (risk_downPolicy_le P fee hfee n k policy ν) penalty

theorem freshPaidPenalty_le_image_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee n k penalty ≤
      paidPenaltyObjective (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
        (zeroAccounting _) policy.val.rule ν penalty :=
  (paidPenaltyValue_le_policy_any_seed _ _ _ penalty (downPolicy P fee hfee n k policy) ν).trans
    (paidPenaltyObjective_downPolicy_le P fee hfee n k policy ν penalty)

theorem upImage_eq_erase_last (k : ℕ) : upImage k = Finset.univ.erase (Fin.last k) := by
  ext tool
  constructor
  · intro h
    exact Finset.mem_erase.mpr ⟨fun he => last_not_mem_upImage k (he ▸ h), Finset.mem_univ _⟩
  · intro h
    have hne : tool ≠ Fin.last k := (Finset.mem_erase.mp h).1
    have hlt : tool.val < k := by
      have ht := tool.isLt
      by_contra hnot
      apply hne
      apply Fin.ext
      change tool.val = k
      omega
    exact Finset.mem_image.mpr ⟨⟨tool.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩

end RootPaidToolTransport
