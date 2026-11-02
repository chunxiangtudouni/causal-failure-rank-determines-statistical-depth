module

public import PaperProofs.Paid.PDMenu_PaidInputTransport_038
public import PaperProofs.Paid.RootPaidToolTransport005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem successor_suffix_instance (n k : ℕ) :
    freshInstance n k = (freshInstance (n + 1) k).freshSuffix 1 := by
  simpa only [Nat.add_sub_cancel] using (freshInstance_suffix_eq (n + 1) k 1).symm

theorem successor_suffix_input (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    HEq (P.freshInput n k fee hfee) ((P.freshInput (n + 1) k fee hfee).freshSuffix 1) := by
  exact (freshInput_suffix_heq P (n + 1) k 1 fee hfee).symm

/-- A true child policy is transported to the original next-stage input. -/
noncomputable def freshGoodSuffixPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed) :
    AvailablePolicy ((P.freshInput (n + 1) k fee hfee).freshSuffix 1)
      (paidRelaxedContract _) (zeroNormalAccounting _) Finset.univ Seed :=
  transportPaidAvailable (successor_suffix_instance n k)
    (P.freshInput n k fee hfee) ((P.freshInput (n + 1) k fee hfee).freshSuffix 1)
    (successor_suffix_input P n k fee hfee) Finset.univ Finset.univ HEq.rfl
    ⟨source, usesOnly_univ _ _ _ _⟩

theorem freshGoodSuffixPolicy_objective (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective ((P.freshInput (n + 1) k fee hfee).freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) (freshGoodSuffixPolicy P fee hfee n k source).val.rule ν penalty =
      paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _)
        source.rule ν penalty :=
  paidPenaltyObjective_transportPaidAvailable _ _ _ _ _ _ _ _ _ _

/-- The corrected head actually consumes last; the child only allocates the
injected old tools. The native rule and all its actual charges are retained. -/
noncomputable def freshBadSuffixPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed) :
    AvailablePolicy ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1)
      (paidRelaxedContract _) (zeroNormalAccounting _) (Finset.univ.erase (Fin.last k)) Seed := by
  let up := RootPaidToolTransport.upPolicy P fee hfee n k source
  have havailable : RootPaidToolTransport.upImage k ⊆ Finset.univ.erase (Fin.last k) := by
    intro tool htool
    exact Finset.mem_erase.mpr ⟨fun he => RootPaidToolTransport.last_not_mem_upImage k (he ▸ htool),
      Finset.mem_univ _⟩
  let child : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroNormalAccounting _) (Finset.univ.erase (Fin.last k)) Seed :=
    ⟨up.val, UsesOnly.mono _ _ _ _ up.property havailable⟩
  exact transportPaidAvailable (successor_suffix_instance n (k + 1))
    (P.freshInput n (k + 1) fee hfee) ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1)
    (successor_suffix_input P n (k + 1) fee hfee)
    (Finset.univ.erase (Fin.last k)) (Finset.univ.erase (Fin.last k)) HEq.rfl child

theorem freshBadSuffixPolicy_objective_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    paidPenaltyObjective ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) (freshBadSuffixPolicy P fee hfee n k source).val.rule ν penalty ≤
      paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _)
        source.rule ν penalty := by
  dsimp only [freshBadSuffixPolicy]
  apply (paidPenaltyObjective_transportPaidAvailable _ _ _ _ _ _ _ _ ν penalty).le.trans
  exact RootPaidToolTransport.paidPenaltyObjective_upPolicy_le P fee hfee n k source ν penalty

end PDMenu


