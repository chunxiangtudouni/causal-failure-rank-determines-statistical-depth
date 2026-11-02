module

public import PaperProofs.Structure.AlgorithmClaims
import Mathlib.Tactic.Linarith

/-! Explicit polynomial address/value bounds in the original logarithmic
word width. These lemmas only discharge numeric safety; they do not supply
an algorithm, memory access certificate, or execution-cost premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.AlgorithmClaims

theorem dimensionPower_le_wordLimit (factor N q : Nat) :
    (N + q + 2) ^ factor ≤ 2 ^ indexWidth factor N q := by
  calc
    _ ≤ (2 ^ Nat.clog 2 (N + q + 2)) ^ factor :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) (N + q + 2)) factor
    _ = _ := by rw [← pow_mul, indexWidth, Nat.mul_comm factor]

theorem fits_indexWidth_of_lt_power (factor N q value : Nat)
    (hvalue : value < (N + q + 2) ^ factor) : Fits (indexWidth factor N q) value :=
  hvalue.trans_le (dimensionPower_le_wordLimit factor N q)

theorem quadratic_add_lt_power16 (base : Nat) (hbase : 2 ≤ base) :
    base ^ 2 + 1024 < base ^ 16 := by
  have hs : 4 ≤ base ^ 2 := Nat.pow_le_pow_left hbase 2
  have hp : 16384 ≤ base ^ 14 := Nat.pow_le_pow_left hbase 14
  calc
    _ < base ^ 2 * 16384 := by nlinarith
    _ ≤ base ^ 2 * base ^ 14 := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [← pow_add]

theorem fits_checker_register_bound (N q : Nat) :
    Fits (indexWidth 16 N q) (N * q + N + q + 640) := by
  apply fits_indexWidth_of_lt_power
  have hs : N * q + N + q + 640 ≤ (N + q + 2) ^ 2 + 1024 := by nlinarith
  exact hs.trans_lt (quadratic_add_lt_power16 (N + q + 2) (by omega))

theorem fits_checker_footprint (N q : Nat) :
    Fits (indexWidth 16 N q) (N * q + 645) := by
  apply fits_indexWidth_of_lt_power
  have hs : N * q + 645 ≤ (N + q + 2) ^ 2 + 1024 := by nlinarith
  exact hs.trans_lt (quadratic_add_lt_power16 (N + q + 2) (by omega))

theorem fits_checker_code_word (N q value : Nat) (hvalue : value ≤ 630) :
    Fits (indexWidth 16 N q) value :=
  lt_of_le_of_lt (hvalue.trans (by omega)) (fits_checker_register_bound N q)

end PaperProofs.Structure.LaminarTree.AlgorithmClaims
