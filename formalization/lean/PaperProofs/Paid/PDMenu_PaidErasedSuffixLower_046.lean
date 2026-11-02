module

public import PaperProofs.Paid.PDMenu_FreshSuffixPolicies_041
public import PaperProofs.Paid.RootPaidToolDelete012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Remove any unavailable head tool from an actual suffix policy. This uses
the genuine native deletion implementation and the exact original input
transport, and keeps the full paid objective on every path. -/
theorem freshPaidPenalty_le_erased_suffix_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) {Seed : Type*} [MeasurableSpace Seed] (tool : Fin (k + 1))
    (source : AvailablePolicy ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1)
      (paidRelaxedContract _) (zeroNormalAccounting _) (Finset.univ.erase tool) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    P.freshPaidPenalty fee hfee n k penalty ≤
      paidPenaltyObjective ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1)
        (paidRelaxedContract _) (zeroNormalAccounting _) source.val.rule ν penalty := by
  let child := transportPaidAvailable (successor_suffix_instance n (k + 1)).symm
    ((P.freshInput (n + 1) (k + 1) fee hfee).freshSuffix 1) (P.freshInput n (k + 1) fee hfee)
    (successor_suffix_input P n (k + 1) fee hfee).symm
    (Finset.univ.erase tool) (Finset.univ.erase tool) HEq.rfl source
  exact (RootPaidToolTransport.freshPaidPenalty_le_erased_tool_policy P fee hfee n k tool child ν penalty).trans
    (paidPenaltyObjective_transportPaidAvailable _ _ _ _ _ _ _ source ν penalty).le

end PDMenu
