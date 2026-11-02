module
public import PaperProofs.Common.PSTR_TM_Arithmetic_008
public import PaperProofs.Common.PSTR_TM_ColumnRewind_067

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Value068
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics

/-- The ORIGINAL first threshold exponent, expressed in its original
positive numerator/denominator fields. Not an extra input/cost field. -/
def exponent (numerator denominator : Nat) : Nat := Nat.clog 2 ⌈(denominator : Rat) / numerator⌉₊

theorem exponent_le_iff (numerator denominator count : Nat) (hn : 0 < numerator) :
    exponent numerator denominator ≤ count ↔ denominator ≤ numerator * 2^count := by
  have hp : (0 : Rat) < numerator := by exact_mod_cast hn
  rw [exponent, Nat.clog_le_iff_le_pow (by decide : 1 < 2), Nat.ceil_le, div_le_iff₀ hp]
  norm_cast
  simp only [Nat.mul_comm]

theorem exponent_stop (numerator denominator : Nat) (hn : 0 < numerator) :
    denominator ≤ numerator * 2^(exponent numerator denominator) :=
  (exponent_le_iff numerator denominator _ hn).mp le_rfl

theorem exponent_strict_before (numerator denominator count : Nat) (hn : 0 < numerator)
    (hc : count < exponent numerator denominator) : numerator * 2^count < denominator := by
  apply Nat.lt_of_not_ge
  intro h
  exact (Nat.not_le.mpr hc) ((exponent_le_iff numerator denominator count hn).mpr h)

/-- The loop performs at most ORIGINAL denominator BIT length many
doublings. No numerical denominator/quota bound is substituted for it. -/
theorem exponent_le_bits (numerator denominator : Nat) (hn : 0 < numerator) :
    exponent numerator denominator ≤ natBits denominator := by
  apply (exponent_le_iff numerator denominator _ hn).mpr
  have hb := PSTRTMCodec001.natBits_bound denominator
  have hm := Nat.mul_le_mul_right (2^natBits denominator) (show 1 ≤ numerator by omega)
  simp only [one_mul] at hm
  omega

theorem counter_bits_le (numerator denominator : Nat) (hn : 0 < numerator) :
    natBits (exponent numerator denominator) ≤ natBits (natBits denominator) :=
  PSTRTMArithmetic008.natBits_mono (exponent_le_bits numerator denominator hn)

/-- The ONE actually allocated extra high column suffices on every
strict-less iteration: doubling stays below its true binary capacity. -/
theorem doubled_strict_before_capacity (numerator denominator count : Nat) (hn : 0 < numerator)
    (hc : count < exponent numerator denominator) :
    2 * (numerator * 2^count) < 2^(max (natBits numerator) (natBits denominator) + 1) := by
  have hs := exponent_strict_before numerator denominator count hn hc
  have hb := PSTRTMCodec001.natBits_bound denominator
  have hm : 2^natBits denominator ≤ 2^max (natBits numerator) (natBits denominator) :=
    Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  rw [Nat.pow_succ]
  nlinarith

theorem controllerB_one_ratio (numerator denominator : Nat) :
    controllerB ((numerator : Rat) / denominator) 1 = exponent numerator denominator := by
  rw [controllerB_one]
  simp [exponent]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Value068
