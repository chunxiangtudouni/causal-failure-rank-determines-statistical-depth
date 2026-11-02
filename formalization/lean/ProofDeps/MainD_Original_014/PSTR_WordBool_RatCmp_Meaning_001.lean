module

public import PSTR_WordBool_RatCmp_Code_001

/-! The reader's finite Boolean accumulator detects canonical zero;
negative-or-zero of the real x-y packet is exactly signed x≤y. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader

open RationalControllerComputation PA17TMRatArithmeticParse002

def anyTrue : List Bool → Bool
  | []=>false
  | bit::later=>bit || anyTrue later

theorem anyTrue_zero_iff (digits : List Bool) : anyTrue digits=false ↔ PSTRTMIncrement009.valueDigits digits=0 := by
  induction digits with
  | nil => simp [anyTrue,PSTRTMIncrement009.valueDigits]
  | cons bit later ih =>
    cases bit <;> simp [anyTrue,PSTRTMIncrement009.valueDigits,Nat.bit,ih]

theorem anyTrue_numerator_zero (value : Rat) : anyTrue (numeratorDigits value)=false ↔ value=0 := by
  rw [anyTrue_zero_iff,numeratorDigits_value,Int.natAbs_eq_zero,Rat.num_eq_zero]

def decision (value : Rat) : Bool := sign value || !anyTrue (numeratorDigits value)

theorem decision_nonpos (value : Rat) : decision value=decide (value≤0) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decision,Bool.or_eq_true,sign,decide_eq_true_eq,Bool.not_eq_true',anyTrue_numerator_zero] using
    (le_iff_lt_or_eq : value≤0 ↔ value<0 ∨ value=0).symm

theorem decision_le (x y : Rat) : decision (x-y)=decide (x≤y) := by
  rw [decision_nonpos]
  simp only [sub_nonpos]

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader
