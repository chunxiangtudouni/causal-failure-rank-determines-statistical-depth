module

public import PaperProofs.Paid.RootPaidToolRename011

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

theorem image_erase_equiv {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) (tool : α) :
    (Finset.univ.erase tool).image e = Finset.univ.erase (e tool) := by
  ext value
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp ha).1 (e.injective he), Finset.mem_univ _⟩
  · intro h
    refine Finset.mem_image.mpr ⟨e.symm value, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩,
      e.apply_symm_apply value⟩
    intro he
    exact (Finset.mem_erase.mp h).1 ((e.apply_symm_apply value).symm.trans (congrArg e he))

theorem erased_swap_image (n k : ℕ) (tool : (freshInstance n (k + 1)).Tool) :
    (Finset.univ.erase tool).image (Equiv.swap tool (Fin.last k)) = upImage k := by
  have he : Equiv.swap tool (Fin.last k) tool = Fin.last k := Equiv.swap_apply_left _ _
  exact (image_erase_equiv (Equiv.swap tool (Fin.last k)) tool).trans
    ((congrArg (fun t => Finset.univ.erase t) he).trans (upImage_eq_erase_last k).symm)

def imagePolicyOfErased (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (tool : (freshInstance n (k + 1)).Tool)
    (source : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (Finset.univ.erase tool) Seed) :
    AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) (zeroAccounting _) (upImage k) Seed :=
  let renamed := RootPaidToolRename.policy P fee hfee n (k + 1)
    (Equiv.swap tool (Fin.last k)) (Finset.univ.erase tool) source
  ⟨renamed.val, by
    intro seed truth tapes time s hp ha handle chosen haction
    have hm := renamed.property seed truth tapes time s hp ha handle chosen haction
    exact erased_swap_image n k tool ▸ hm⟩

def deletePolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (tool : (freshInstance n (k + 1)).Tool)
    (source : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (Finset.univ.erase tool) Seed) :
    Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed :=
  downPolicy P fee hfee n k (imagePolicyOfErased P fee hfee n k tool source)

theorem deletePolicy_actualBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (tool : (freshInstance n (k + 1)).Tool)
    (source : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (Finset.univ.erase tool) Seed)
    (sample : Seed × (P.freshInput n (k + 1) fee hfee).World) :
    runActualBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (deletePolicy P fee hfee n k tool source).rule (downSample P fee hfee n k sample) =
      runActualBill (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) source.val.rule sample :=
  (runActualBill_downPolicy P fee hfee n k (imagePolicyOfErased P fee hfee n k tool source) sample).trans
    (RootPaidToolRename.runActualBill_policy P fee hfee n (k + 1)
      (Equiv.swap tool (Fin.last k)) (Finset.univ.erase tool) source sample)

theorem deletePolicy_paidObjective_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (tool : (freshInstance n (k + 1)).Tool)
    (source : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (Finset.univ.erase tool) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _)
      (deletePolicy P fee hfee n k tool source).rule ν penalty ≤
      paidPenaltyObjective (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
        (zeroAccounting _) source.val.rule ν penalty :=
  (paidPenaltyObjective_downPolicy_le P fee hfee n k (imagePolicyOfErased P fee hfee n k tool source) ν penalty).trans
    (RootPaidToolRename.paidObjective_policy_le P fee hfee n (k + 1)
      (Equiv.swap tool (Fin.last k)) (Finset.univ.erase tool) source ν penalty)

/-- Actual erased-tool policy -> original independently defined F, retaining
all original n/k, arbitrary private seeds and the entire extended paid bill. -/
theorem freshPaidPenalty_le_erased_tool_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (tool : (freshInstance n (k + 1)).Tool)
    (source : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (Finset.univ.erase tool) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee n k penalty ≤
      paidPenaltyObjective (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
        (zeroAccounting _) source.val.rule ν penalty :=
  (paidPenaltyValue_le_policy_any_seed _ _ _ penalty (deletePolicy P fee hfee n k tool source) ν).trans
    (deletePolicy_paidObjective_le P fee hfee n k tool source ν penalty)

end RootPaidToolTransport
