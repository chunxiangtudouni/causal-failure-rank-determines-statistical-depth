module

public import Paid.PDROC_CalibrationRow_024

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.CalibrationRow

open PDLower.CalibrationCompute

/-- Exact physical orientation after the actual number of swaps. This
is proof-side notation; the ISA program performs the real header swap
and never receives this pair as a prepared input or an oracle. -/
def rowPointers (base M : ℕ) : ℕ → ℕ×ℕ
  | 0 => (firstRow base,secondRow base M)
  | clock+1 => let previous := rowPointers base M clock; (previous.2,previous.1)

theorem rowPointers_zero (base M : ℕ) : rowPointers base M 0=(firstRow base,secondRow base M) := rfl

theorem rowPointers_succ (base M clock : ℕ) :
    rowPointers base M (clock+1)=((rowPointers base M clock).2,(rowPointers base M clock).1) := rfl

theorem rowPointers_buffers (base M clock : ℕ) :
    Buffers base M (rowPointers base M clock).1 (rowPointers base M clock).2 := by
  induction clock with
  | zero => exact Or.inl ⟨rfl,rfl⟩
  | succ clock ih =>
    simpa only [rowPointers_succ] using Buffers.swap base M (rowPointers base M clock).1 (rowPointers base M clock).2 ih

end PDROC.CalibrationRow
