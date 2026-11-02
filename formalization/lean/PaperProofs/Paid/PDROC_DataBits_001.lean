module

public import PaperProofs.Paid.CachedFrontend
public import PaperProofs.Common.PSTR_TM_Arithmetic_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem natBits_pos (n : ℕ) : 0 < natBits n := by simp [natBits]

theorem natBits_lt_pow (n : ℕ) : n < 2 ^ natBits n := Nat.lt_log2_self

theorem natBits_mono {m n : ℕ} (h : m ≤ n) : natBits m ≤ natBits n := by
  simpa only [natBits, PaperProofs.Common.Native.RationalControllerComputation.natBits] using
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMArithmetic008.natBits_mono h

theorem natBits_le_of_lt_pow (n k : ℕ) (h : n < 2 ^ k) (hk : 0 < k) : natBits n ≤ k := by
  simpa only [natBits, PaperProofs.Common.Native.RationalControllerComputation.natBits] using
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMArithmetic008.natBits_le_of_lt_pow n k h hk

theorem natBits_add_le (m n : ℕ) : natBits (m + n) ≤ natBits m + natBits n := by
  simpa only [natBits, PaperProofs.Common.Native.RationalControllerComputation.natBits] using
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMArithmetic008.natBits_add_le m n

theorem natBits_mul_le (m n : ℕ) : natBits (m * n) ≤ natBits m + natBits n := by
  apply natBits_le_of_lt_pow
  · rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (natBits_lt_pow m) (natBits_lt_pow n)
  · exact Nat.add_pos_left (natBits_pos m) _

theorem natBits_pow_le (m n : ℕ) : natBits (m ^ n) ≤ n * natBits m + 1 := by
  have hle : m ^ n ≤ (2 ^ natBits m) ^ n :=
    Nat.pow_le_pow_left (natBits_lt_pow m).le n
  calc
    natBits (m ^ n) ≤ natBits ((2 ^ natBits m) ^ n) := natBits_mono hle
    _ = n * natBits m + 1 := by rw [← pow_mul]; simp [natBits, Nat.log2_two_pow, mul_comm]

theorem natBits_prod_le (values : List ℕ) (hne : values ≠ []) :
    natBits values.prod ≤ (values.map natBits).sum := by
  induction values with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
      cases rest with
      | nil => simp
      | cons second rest =>
          have ht := ih (by simp)
          exact (natBits_mul_le first (second :: rest).prod).trans
            (Nat.add_le_add_left ht (natBits first))

theorem ratDenBits_le_of_dvd {q : ℚ} {D : ℕ} (hD : 0 < D) (h : q.den ∣ D) :
    ratDenBits q ≤ natBits D := natBits_mono (Nat.le_of_dvd hD h)

end PDROC.DataBits
