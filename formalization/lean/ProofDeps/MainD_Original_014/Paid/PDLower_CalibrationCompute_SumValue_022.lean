module

public import Paid.PDLower_CalibrationCompute_ABI_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

def rowPrefixSum (row : Array ℚ) (count : ℕ) : ℚ :=
  ∑ index ∈ Finset.range count,row.getD index 0

theorem rowPrefixSum_zero (row : Array ℚ) : rowPrefixSum row 0 = 0 := by
  simp [rowPrefixSum]

theorem rowPrefixSum_succ (row : Array ℚ) (count : ℕ) :
    rowPrefixSum row (count+1) = rowPrefixSum row count+row.getD count 0 := by
  exact Finset.sum_range_succ _ _

def rowLoss (row : Array ℚ) (level index : ℕ) : ℚ :=
  row.getD index 0 * (if index < level then 1 else if index = level then 1/2 else 0)

theorem sum_rowLoss (row : Array ℚ) (level extra : ℕ) :
    (∑ index ∈ Finset.range (level+1+extra),rowLoss row level index) =
      rowPrefixSum row level+row.getD level 0*(1/2) := by
  induction extra with
  | zero =>
    simp only [Nat.add_zero,Finset.sum_range_succ]
    have below : (∑ index ∈ Finset.range level,rowLoss row level index) = rowPrefixSum row level := by
      apply Finset.sum_congr rfl
      intro index inside
      simp [rowLoss,Finset.mem_range.mp inside]
    rw [below]
    simp [rowLoss]
  | succ extra ih =>
    rw [Nat.add_succ,Finset.sum_range_succ,ih]
    have notBelow : ¬level+1+extra < level := by omega
    have notCenter : level+1+extra ≠ level := by omega
    simp [rowLoss,notBelow,notCenter]

theorem cachedCappedError_eq_prefix (P : Parameters) (m : ℕ) :
    P.cachedCappedError m =
      rowPrefixSum (P.walkRow (m+1) true P.certificate.Q) (m+1)+
        (P.walkRow (m+1) true P.certificate.Q).getD (m+1) 0*(1/2) := by
  change (∑ state : Fin (2*(m+1)+1),rowLoss (P.walkRow (m+1) true P.certificate.Q) (m+1) state.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have width : 2*(m+1)+1 = (m+1)+1+(m+1) := by omega
  rw [width,sum_rowLoss]

end PDLower.CalibrationCompute
