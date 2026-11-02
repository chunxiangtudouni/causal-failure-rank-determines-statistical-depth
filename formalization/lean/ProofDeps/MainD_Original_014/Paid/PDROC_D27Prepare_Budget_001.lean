module

public import PaperProofs.Paid.ComputationalClaims
public import PaperProofs.Paid.PDROC_DataBits_Search_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.D27Prepare.Budget

def originalRatio (P : Parameters) (fee : ℚ) : ℚ :=
  2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee

theorem ratio_nonpositive (P : Parameters) (fee : ℚ)
    (h : P.positiveValueFloor fee ≤ 0) : originalRatio P fee ≤ 0 := by
  exact div_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num) P.Lambda_pos.le) P.certificate.risk_pos.le) h

/-- The original total rational division is respected even at floor=0.
The actual ISA takes the other branch and never executes division by zero. -/
theorem budget_zero_of_floor_nonpositive (P : Parameters) (fee : ℚ)
    (h : P.positiveValueFloor fee ≤ 0) : P.bisectionBudget fee = 0 := by
  change Nat.clog 2 (Nat.ceil (originalRatio P fee)) = 0
  rw [Nat.ceil_eq_zero.mpr (ratio_nonpositive P fee h), Nat.clog_zero_right]

theorem ratio_pos (P : Parameters) (fee : ℚ)
    (h : 0 < P.positiveValueFloor fee) : 0 < originalRatio P fee := by
  exact div_pos (mul_pos (mul_pos (by norm_num) P.Lambda_pos) P.certificate.risk_pos) h

/-- Potential for the actual page43/44 halving loop. -/
def remaining (x : ℕ) : ℕ := Nat.clog 2 (x + 1)

theorem remaining_zero : remaining 0 = 0 := by simp [remaining]

theorem remaining_step (x : ℕ) (hx : 0 < x) :
    remaining x = remaining (x / 2) + 1 := by
  have h := Nat.clog_of_one_lt (b := 2) (n := x + 1) (by omega) (by omega)
  have half : (x + 1 + 2 - 1) / 2 = x / 2 + 1 := by omega
  simpa only [remaining, half] using h

theorem remaining_start (ceiling : ℕ) : remaining (ceiling - 1) = Nat.clog 2 ceiling := by
  by_cases h : ceiling = 0
  · subst ceiling
    simp [remaining]
  · have heq : ceiling - 1 + 1 = ceiling := by omega
    simp only [remaining, heq]

theorem remaining_le_bits (x : ℕ) : remaining x ≤ natBits x := by
  apply (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).mpr
  exact Nat.succ_le_of_lt (PDROC.DataBits.natBits_lt_pow x)

theorem remaining_pos (x : ℕ) (hx : 0 < x) : 0 < remaining x := by
  exact Nat.clog_pos (by omega) (by omega)

theorem halve_lt (x : ℕ) (hx : 0 < x) : x / 2 < x := Nat.div_lt_self hx (by omega)

theorem iteration_invariant (j x target : ℕ) (hx : 0 < x)
    (h : j + remaining x = target) : j + 1 + remaining (x / 2) = target := by
  rw [remaining_step x hx] at h
  omega

theorem iteration_values (ceiling j x : ℕ) (hx : x ≤ ceiling)
    (h : j + remaining x = Nat.clog 2 ceiling) :
    x / 2 ≤ ceiling ∧ j ≤ Nat.clog 2 ceiling ∧
      remaining x ≤ natBits ceiling := by
  exact ⟨(Nat.div_le_self _ _).trans hx, by omega,
    (remaining_le_bits x).trans (PDROC.DataBits.natBits_mono hx)⟩

theorem finished_value (j target : ℕ) (h : j + remaining 0 = target) : j = target := by
  simpa only [remaining_zero, Nat.add_zero] using h

end PDROC.D27Prepare.Budget
