module

public import Common.PSTR_TM_NatValue_017

/-! Structural binary long-division algebra shared by the quotient and
remainder kernels. Nat.div/mod occur only in the correctness statement.
The actual machine must realize each emitted bit by compare and at most
one subtraction; these ghost recurrences are not supplied machine inputs. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

open PSTRTMIncrement009

def quotientBit (divisor remainder : Nat) (bit : Bool) : Bool :=
  decide (0 < divisor ∧ divisor ≤ 2 * remainder + bit.toNat)

def pushBit (divisor : Nat) (bit : Bool) (previous : Nat × Nat) : Nat × Nat :=
  let emitted := quotientBit divisor previous.2 bit
  (2 * previous.1 + emitted.toNat,
    if emitted then 2 * previous.2 + bit.toNat - divisor else 2 * previous.2 + bit.toNat)

/-- LSB-first source: the higher tail is processed first, exactly MSB-first
long division, with one emitted quotient bit at each original source bit. -/
def quotRem (divisor : Nat) : List Bool → Nat × Nat
  | [] => (0, 0)
  | bit :: higher => pushBit divisor bit (quotRem divisor higher)

def quotientDigits (divisor : Nat) : List Bool → List Bool
  | [] => []
  | bit :: higher => quotientBit divisor (quotRem divisor higher).2 bit :: quotientDigits divisor higher

theorem bit_value (bit : Bool) (value : Nat) : Nat.bit bit value = 2 * value + bit.toNat := by
  cases bit <;> simp [Nat.bit]

theorem next_remainder_lt_twice {divisor remainder : Nat} (bit : Bool)
    (hr : remainder < divisor) : 2 * remainder + bit.toNat < 2 * divisor := by
  have hb := Bool.toNat_le bit
  omega

theorem pushBit_invariant (divisor quotient remainder : Nat) (bit : Bool)
    (hd : 0 < divisor) (hr : remainder < divisor) :
    divisor * (pushBit divisor bit (quotient, remainder)).1 + (pushBit divisor bit (quotient, remainder)).2 =
      2 * (divisor * quotient + remainder) + bit.toNat ∧
      (pushBit divisor bit (quotient, remainder)).2 < divisor := by
  have upper := next_remainder_lt_twice bit hr
  by_cases take : divisor ≤ 2 * remainder + bit.toNat
  · have emitted : quotientBit divisor remainder bit = true := by simp [quotientBit, hd, take]
    simp only [pushBit, emitted, Bool.toNat_true, ite_true]
    have balance := Nat.sub_add_cancel take
    constructor <;> nlinarith
  · have emitted : quotientBit divisor remainder bit = false := by simp [quotientBit, take]
    simp only [pushBit, emitted, Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ite_false]
    constructor
    · ring
    · omega

theorem quotRem_invariant (divisor : Nat) (bits : List Bool) (hd : 0 < divisor) :
    divisor * (quotRem divisor bits).1 + (quotRem divisor bits).2 = valueDigits bits ∧
      (quotRem divisor bits).2 < divisor := by
  induction bits with
  | nil => exact ⟨rfl, hd⟩
  | cons bit higher ih =>
    have step := pushBit_invariant divisor (quotRem divisor higher).1 (quotRem divisor higher).2 bit hd ih.2
    constructor
    · simpa only [quotRem, valueDigits, bit_value, ih.1] using step.1
    · exact step.2

theorem quotRem_zero (bits : List Bool) : quotRem 0 bits = (0, valueDigits bits) := by
  induction bits with
  | nil => rfl
  | cons bit higher ih =>
    simp only [quotRem, ih, pushBit, quotientBit, Nat.lt_irrefl, false_and, decide_false,
      Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ite_false, valueDigits, bit_value]

theorem quotRem_correct (divisor : Nat) (bits : List Bool) :
    quotRem divisor bits = (valueDigits bits / divisor, valueDigits bits % divisor) := by
  by_cases zero : divisor = 0
  · subst divisor
    rw [quotRem_zero]
    simp only [Nat.div_zero, Nat.mod_zero]
  · have positive : 0 < divisor := Nat.pos_of_ne_zero zero
    have invariant := quotRem_invariant divisor bits positive
    have unique : valueDigits bits / divisor = (quotRem divisor bits).1 ∧
        valueDigits bits % divisor = (quotRem divisor bits).2 :=
      (Nat.div_mod_unique positive).mpr ⟨by omega, invariant.2⟩
    exact Prod.ext unique.1.symm unique.2.symm

theorem quotientDigits_length (divisor : Nat) (bits : List Bool) :
    (quotientDigits divisor bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit higher ih => simp only [quotientDigits, List.length_cons, ih]

theorem quotientDigits_value (divisor : Nat) (bits : List Bool) :
    valueDigits (quotientDigits divisor bits) = (quotRem divisor bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit higher ih =>
    simp only [quotientDigits, valueDigits, bit_value, ih, quotRem, pushBit]

theorem original_payload_correct (dividend divisor : Nat) :
    quotRem divisor (PSTRTMNatValue017.rawPayload dividend) = (dividend / divisor, dividend % divisor) := by
  rw [quotRem_correct, PSTRTMNatValue017.valueDigits_rawPayload]

theorem no_positive_shift_overflow {width divisor remainder : Nat} (bit : Bool)
    (hr : remainder < divisor) (room : 2 * divisor ≤ 2 ^ width) :
    2 * remainder + bit.toNat < 2 ^ width :=
  (next_remainder_lt_twice bit hr).trans_le room

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
