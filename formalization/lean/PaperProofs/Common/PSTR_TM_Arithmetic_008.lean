module
public import PaperProofs.Common.PSTR_TM_Length_004
public import Mathlib.Data.Rat.Lemmas

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMArithmetic008
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCodec001 PSTRTMLength004

theorem natBits_mono {m n : Nat} (h : m ≤ n) : natBits m ≤ natBits n := by
  simp only [natBits, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem natBits_le_of_lt_pow (n k : Nat) (h : n < 2 ^ k) (hk : 0 < k) : natBits n ≤ k := by
  by_cases hn : n = 0
  · subst n
    simpa [natBits] using (Nat.succ_le_of_lt hk)
  · have hl := (Nat.log2_lt hn).mpr h
    simp only [natBits]
    omega

/-- Bit-length growth is bounded in original operands, never in an output
leaf maximum passed as an extra input. Zero operands are included. -/
theorem natBits_add_le (m n : Nat) : natBits (m + n) ≤ natBits m + natBits n := by
  have hm := natBits_bound m
  have hn := natBits_bound n
  have hmp : 0 < natBits m := by simp [natBits]
  have hnp : 0 < natBits n := by simp [natBits]
  have hm2 : 2 ≤ 2 ^ natBits m := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hmp
  have hn2 : 2 ≤ 2 ^ natBits n := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hnp
  have hp := Nat.mul_le_mul_left (2 ^ natBits m) hn2
  have hq := Nat.mul_le_mul_right (2 ^ natBits n) hm2
  apply natBits_le_of_lt_pow
  · rw [Nat.pow_add]
    omega
  · omega

theorem one_sub_den (value : Rat) : (1 - value).den = value.den := by simp

theorem one_sub_num (value : Rat) : (1 - value).num = (value.den : Int) - value.num := by
  apply mul_right_cancel₀ (show (value.den : Int) ≠ 0 by exact_mod_cast value.den_ne_zero)
  simpa using Rat.sub_num_den' 1 value

theorem one_sub_num_abs_le (value : Rat) :
    (1 - value).num.natAbs ≤ value.den + value.num.natAbs := by
  rw [one_sub_num]
  simpa using Int.natAbs_sub_le (value.den : Int) value.num

theorem one_sub_num_bits_le (value : Rat) :
    natBits (1 - value).num.natAbs ≤ natBits value.den + natBits value.num.natAbs :=
  (natBits_mono (one_sub_num_abs_le value)).trans (natBits_add_le _ _)

/-- The false-prior leaf used by the ORIGINAL symbolic AST has at most
 twice the encoded rational bit length of its raw priorOne input. -/
theorem one_sub_datumBits_le (value : Rat) :
    datumBits (.rational (1 - value)) ≤ 2 * datumBits (.rational value) := by
  have h := one_sub_num_bits_le value
  simp only [datumBits, one_sub_den]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMArithmetic008

