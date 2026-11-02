module
public import Structure.PA17_TM_RatArithmetic_Semantics_001d
public import Common.PSTR_TM_Arithmetic_008

/-! Bit lengths are charged to the exact original two-rational input.
No candidate value, width, gcd or answer is an extra original input. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeSize007
open PA17TMRatArithmeticSemantics001 PSTRTMArithmetic008 PSTRTMCodec001 PSTRTMLength004

def inputBits (x y : Rat) : Nat :=
  natBits x.num.natAbs + natBits x.den + natBits y.num.natAbs + natBits y.den

theorem natBits_positive (n : Nat) : 0 < natBits n := by
  simp only [natBits]
  omega

theorem natBits_mul_le (m n : Nat) : natBits (m*n) ≤ natBits m + natBits n := by
  apply natBits_le_of_lt_pow
  · rw [Nat.pow_add]
    exact (Nat.mul_le_mul_left m (Nat.le_of_lt (natBits_bound n))).trans_lt
      (Nat.mul_lt_mul_of_pos_right (natBits_bound m) (Nat.pow_pos (by decide)))
  · have hm := natBits_positive m
    omega

theorem input_length (x y : Rat) :
    (encode [.rational x,.rational y]).length = 2 * inputBits x y + 14 := by
  rw [rational_pair_encoding]
  simp only [List.length_append,List.length_singleton,encodeNat_length,
    encodeDatum_rational_length]
  have ht : natBits 2 = 2 := rfl
  rw [ht]
  unfold inputBits
  omega

theorem inputBits_le_input_length (x y : Rat) :
    inputBits x y ≤ (encode [.rational x,.rational y]).length := by
  rw [input_length]
  omega

theorem inputBits_positive (x y : Rat) : 0 < inputBits x y := by
  have hx := natBits_positive x.num.natAbs
  unfold inputBits
  omega

theorem sumMag_le_add (sx sy : Bool) (a b : Nat) : sumMag sx sy a b ≤ a+b := by
  by_cases hs : sx = sy
  · simp [sumMag,hs]
  · by_cases hab : a < b
    · rw [sumMag,ite_eq_right hs,ite_eq_left hab]
      omega
    · rw [sumMag,ite_eq_right hs,ite_eq_right hab]
      omega

theorem sumMag_bits_le (sx sy : Bool) (a b : Nat) :
    natBits (sumMag sx sy a b) ≤ natBits a + natBits b :=
  (natBits_mono (sumMag_le_add sx sy a b)).trans (natBits_add_le a b)

theorem crossLeft_bits_le (x y : Rat) :
    natBits (crossLeft x y) ≤ natBits x.num.natAbs + natBits y.den :=
  natBits_mul_le _ _

theorem crossRight_bits_le (x y : Rat) :
    natBits (crossRight x y) ≤ natBits y.num.natAbs + natBits x.den :=
  natBits_mul_le _ _

theorem addMagnitude_bits_le (x y : Rat) : natBits (addMagnitude x y) ≤ inputBits x y := by
  have hs := sumMag_bits_le (decide (x<0)) (decide (y<0)) (crossLeft x y) (crossRight x y)
  have hl := crossLeft_bits_le x y
  have hr := crossRight_bits_le x y
  change natBits (sumMag _ _ _ _) ≤ _
  unfold inputBits
  omega

theorem subMagnitude_bits_le (x y : Rat) : natBits (subMagnitude x y) ≤ inputBits x y := by
  have hs := sumMag_bits_le (decide (x<0)) (!decide (y<0)) (crossLeft x y) (crossRight x y)
  have hl := crossLeft_bits_le x y
  have hr := crossRight_bits_le x y
  change natBits (sumMag _ _ _ _) ≤ _
  unfold inputBits
  omega

theorem mulMagnitude_bits_le (x y : Rat) :
    natBits (x.num.natAbs*y.num.natAbs) ≤ inputBits x y := by
  have hm := natBits_mul_le x.num.natAbs y.num.natAbs
  unfold inputBits
  omega

theorem divMagnitude_bits_le (x y : Rat) : natBits (divMagnitude x y) ≤ inputBits x y := by
  have hl : divMagnitude x y ≤ crossLeft x y := by
    by_cases hz : y.num.natAbs = 0 <;> simp [divMagnitude,crossLeft,hz]
  have hm := (natBits_mono hl).trans (crossLeft_bits_le x y)
  unfold inputBits
  omega

theorem productDen_bits_le (x y : Rat) : natBits (productDen x y) ≤ inputBits x y := by
  have hm := natBits_mul_le x.den y.den
  change natBits (x.den*y.den) ≤ _
  unfold inputBits
  omega

theorem quotientDen_bits_le (x y : Rat) : natBits (quotientDen x y) ≤ inputBits x y := by
  have hm := natBits_mul_le x.den y.num.natAbs
  change natBits (x.den*y.num.natAbs) ≤ _
  unfold inputBits
  omega

theorem raw_fields_bits_le_input (x y : Rat) :
    natBits (crossLeft x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (crossRight x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (addMagnitude x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (subMagnitude x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x.num.natAbs*y.num.natAbs) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (divMagnitude x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (productDen x y) ≤ (encode [.rational x,.rational y]).length ∧
    natBits (quotientDen x y) ≤ (encode [.rational x,.rational y]).length := by
  have hi := inputBits_le_input_length x y
  have hl := crossLeft_bits_le x y
  have hr := crossRight_bits_le x y
  have ha := (addMagnitude_bits_le x y).trans hi
  have hs := (subMagnitude_bits_le x y).trans hi
  have hm := (mulMagnitude_bits_le x y).trans hi
  have hd := (divMagnitude_bits_le x y).trans hi
  have hp := (productDen_bits_le x y).trans hi
  have hq := (quotientDen_bits_le x y).trans hi
  unfold inputBits at hi
  exact ⟨by omega,by omega,ha,hs,hm,hd,hp,hq⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeSize007
