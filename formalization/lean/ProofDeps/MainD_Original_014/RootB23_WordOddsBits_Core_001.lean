module

public import B23_4_RatWordPrep_SeqCmp_WordPublic_015

/-! Total canonical rational field width.  Multiplication and division
add operand widths with coefficient one, including the zero-divisor case. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB23.WordOddsBits

open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool
open PA17TMRatArithmeticSemantics001 PA17TMRatArithmeticNativeSize007
open PSTRTMArithmetic008 PA17TMRatArithmeticParse002

def width (q : Rat) : Nat := natBits q.num.natAbs + natBits q.den

@[simp] theorem width_one : width 1 = 2 := rfl

@[simp] theorem width_zero : width 0 = 2 := rfl

theorem width_pos (q : Rat) : 0 < width q := by
  have h := natBits_positive q.den
  unfold width
  omega

theorem mul_width_le (x y : Rat) : width (x*y) ≤ width x + width y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (mul_signed_value x y)
  have hn := hm.trans (natBits_mul_le x.num.natAbs y.num.natAbs)
  change natBits (x*y).den ≤ natBits (x.den*y.den) at hd
  have hd' := hd.trans (natBits_mul_le x.den y.den)
  unfold width
  omega

theorem div_width_le (x y : Rat) : width (x/y) ≤ width x + width y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (div_signed_value x y)
  have raw : divMagnitude x y ≤ x.num.natAbs*y.den := by
    by_cases hz : y.num.natAbs = 0 <;> simp [divMagnitude,hz]
  have hn := hm.trans ((natBits_mono raw).trans (natBits_mul_le x.num.natAbs y.den))
  change natBits (x/y).den ≤ natBits (x.den*y.num.natAbs) at hd
  have hd' := hd.trans (natBits_mul_le x.den y.num.natAbs)
  unfold width
  omega

theorem one_sub_width_le (q : Rat) : width (1-q) ≤ 2*width q := by
  have hn := one_sub_num_bits_le q
  unfold width
  rw [one_sub_den]
  omega

theorem foldl_mul_width_le (xs : List Rat) (init : Rat) :
    width (xs.foldl (fun a q => a*q) init) ≤ width init + (xs.map width).sum := by
  induction xs generalizing init with
  | nil => simp
  | cons q xs ih =>
    have h := ih (init*q)
    have step := mul_width_le init q
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega

theorem foldl_mul_prefix_width_le (xs : List Rat) (init : Rat) (k : Nat) :
    width ((xs.take k).foldl (fun a q => a*q) init) ≤
      width init + ((xs.take k).map width).sum :=
  foldl_mul_width_le (xs.take k) init

theorem list_prod_width_le (xs : List Rat) : width xs.prod ≤ 2 + (xs.map width).sum := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    have step := mul_width_le q xs.prod
    simp only [List.prod_cons,List.map_cons,List.sum_cons]
    omega

theorem list_width_sum_le (xs : List Rat) (bound : Nat)
    (bounded : ∀ q ∈ xs, width q ≤ bound) :
    (xs.map width).sum ≤ xs.length*bound := by
  have h := List.sum_le_length_nsmul (xs.map width) bound (by
    intro value member
    obtain ⟨q,present,rfl⟩ := List.mem_map.mp member
    exact bounded q present)
  simpa only [List.length_map,smul_eq_mul] using h

theorem ratPair_fieldSize_eq (x y : Rat) :
    RatPair.fieldSize x y = width x + width y := by
  simp only [RatPair.fieldSize,RatPair.Collector.fieldSize,numeratorDigits_length,
    denominatorDigits_length,width]
  omega

theorem ratInput_fieldSize_eq (q : Rat) : RatInput.Encoder.fieldSize q = width q := by
  simp only [RatInput.Encoder.fieldSize,numeratorDigits_length,denominatorDigits_length,width]

end RootB23.WordOddsBits
