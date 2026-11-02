module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Common.FreshSuffixComposition

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

private theorem input_heq_of_fields {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K)
    (hexperiment : HEq left.experiment right.experiment)
    (hcorrection : HEq left.correctionFee right.correctionFee) : HEq left right := by
  cases hI
  cases left with
  | mk lexp lfee lnonneg =>
    cases right with
    | mk rexp rfee rnonneg =>
      have he : lexp = rexp := eq_of_heq hexperiment
      cases he
      have hf : lfee = rfee := eq_of_heq hcorrection
      cases hf
      rfl

/-- Actual shared-pool instance equality, including k>=n and empty suffixes. -/
theorem freshInstance_suffix_eq (n k first : ℕ) :
    (freshInstance n k).freshSuffix first = freshInstance (n - first) k := by
  simp only [freshInstance, Instance.freshSuffix, List.drop_replicate]

theorem freshInput_suffix_heq (P : Parameters) (n k first : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    HEq ((P.freshInput n k fee hfee).freshSuffix first) (P.freshInput (n - first) k fee hfee) := by
  have hI := freshInstance_suffix_eq n k first
  have hStage : ((freshInstance n k).freshSuffix first).Stage = (freshInstance (n - first) k).Stage :=
    congrArg (fun J : Instance => J.Stage) hI
  apply input_heq_of_fields hI
  · apply Function.hfunext hStage
    intro left right _h
    apply heq_of_eq
    rw [StatisticalInput.freshSuffix_experiment]
    rfl
  · apply Function.hfunext hStage
    intro left right _h
    apply heq_of_eq
    funext tool
    exact (P.freshInput n k fee hfee).freshSuffix_correctionFee first left tool

theorem paidPenaltyValue_congr {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right) (penalty : ℝ≥0∞) :
    paidPenaltyValue left (paidRelaxedContract J) (zeroNormalAccounting J) penalty =
      paidPenaltyValue right (paidRelaxedContract K) (zeroNormalAccounting K) penalty := by
  cases hI
  cases eq_of_heq hinput
  rfl

theorem freshPaidPenalty_suffix_eq (P : Parameters) (n k first : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (penalty : ℝ≥0∞) :
    paidPenaltyValue ((P.freshInput n k fee hfee).freshSuffix first)
      (paidRelaxedContract ((freshInstance n k).freshSuffix first))
      (zeroNormalAccounting ((freshInstance n k).freshSuffix first)) penalty =
      P.freshPaidPenalty fee hfee (n - first) k penalty := by
  exact paidPenaltyValue_congr (freshInstance_suffix_eq n k first)
    ((P.freshInput n k fee hfee).freshSuffix first) (P.freshInput (n - first) k fee hfee)
    (freshInput_suffix_heq P n k first fee hfee) penalty

end PDMenu
