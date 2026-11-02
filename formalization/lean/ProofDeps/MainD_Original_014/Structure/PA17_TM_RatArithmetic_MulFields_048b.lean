module
public import Structure.PA17_TM_RatArithmetic_MulFields_048a
public import Structure.PA17_TM_RatArithmetic_Size_007d
public import Structure.PA17_TM_RatArithmetic_NativeCache_030a

/-! All five REAL native-call scales are bounded by original fieldWidth.
The window and scale are the frozen030 definitions; no045 draft is imported. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048

open PA17TMRatArithmeticParse002 PA17TMRatArithmeticNativeSize007
open PA17TMRatArithmeticSemantics001 PA17TMRatArithmeticNativeCache030
open PSTRTMArithmetic008 PSTRTMLength004

theorem inputBits_eq_fieldWidth (x y : Rat) : inputBits x y=fieldWidth x y := by
  have hi := input_length x y
  have hp : (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 := pair_length x y
  omega

theorem fieldWidth_ge_four (x y : Rat) : 4≤fieldWidth x y := by
  obtain ⟨hx,hdx⟩ := field_widths_positive x
  obtain ⟨hy,hdy⟩ := field_widths_positive y
  unfold fieldWidth
  omega

theorem original_field_bits (x y : Rat) :
    natBits x.num.natAbs≤fieldWidth x y ∧ natBits y.num.natAbs≤fieldWidth x y ∧
      natBits x.den≤fieldWidth x y ∧ natBits y.den≤fieldWidth x y := by
  rw [←inputBits_eq_fieldWidth]
  unfold inputBits
  omega

theorem productMagnitude_bits (x y : Rat) : natBits (productMagnitude x y)≤fieldWidth x y := by
  simpa only [productMagnitude,inputBits_eq_fieldWidth] using mulMagnitude_bits_le x y

theorem productDenominator_bits (x y : Rat) : natBits (productDenominator x y)≤fieldWidth x y := by
  simpa only [productDenominator,productDen,inputBits_eq_fieldWidth] using productDen_bits_le x y

theorem normalizer_bits (x y : Rat) : natBits (normalizer x y)≤fieldWidth x y := by
  have hg := natBits_mono (Nat.gcd_le_right (productMagnitude x y) (productDenominator_pos x y))
  exact hg.trans (productDenominator_bits x y)

theorem normalized_bits (x y : Rat) :
    natBits (quotientNumerator x y)≤fieldWidth x y ∧ natBits (quotientDenominator x y)≤fieldWidth x y := by
  exact ⟨(natBits_mono (Nat.div_le_self _ _)).trans (productMagnitude_bits x y),
    (natBits_mono (Nat.div_le_self _ _)).trans (productDenominator_bits x y)⟩

theorem scale_le_four_width (width a b : Nat) (hw : 1≤width)
    (ha : natBits a≤width) (hb : natBits b≤width) : scale a b≤4*width := by
  unfold scale
  omega

theorem five_scales (x y : Rat) :
    scale x.num.natAbs y.num.natAbs≤4*fieldWidth x y ∧
    scale x.den y.den≤4*fieldWidth x y ∧
    scale (productMagnitude x y) (productDenominator x y)≤4*fieldWidth x y ∧
    scale (productMagnitude x y) (normalizer x y)≤4*fieldWidth x y ∧
    scale (productDenominator x y) (normalizer x y)≤4*fieldWidth x y := by
  obtain ⟨hnx,hny,hdx,hdy⟩ := original_field_bits x y
  have hw : 1≤fieldWidth x y := by have h := fieldWidth_ge_four x y;omega
  have hm := productMagnitude_bits x y
  have hd := productDenominator_bits x y
  have hg := normalizer_bits x y
  exact ⟨scale_le_four_width _ _ _ hw hnx hny,scale_le_four_width _ _ _ hw hdx hdy,
    scale_le_four_width _ _ _ hw hm hd,scale_le_four_width _ _ _ hw hm hg,
    scale_le_four_width _ _ _ hw hd hg⟩

theorem actual_five_scales (x y : Rat) (m d g : Nat)
    (hm : m=x.num.natAbs*y.num.natAbs) (hd : d=x.den*y.den) (hg : g=Nat.gcd m d) :
    scale x.num.natAbs y.num.natAbs≤4*fieldWidth x y ∧
    scale x.den y.den≤4*fieldWidth x y ∧ scale m d≤4*fieldWidth x y ∧
    scale m g≤4*fieldWidth x y ∧ scale d g≤4*fieldWidth x y := by
  rw [hg,hm,hd]
  exact five_scales x y

theorem window_bound (x y : Rat) (a b : Nat) (hscale : scale a b≤4*fieldWidth x y) :
    window a b≤524320*(fieldWidth x y)^2 := by
  have hw := fieldWidth_ge_four x y
  have squared := Nat.pow_le_pow_left hscale 2
  have linear : fieldWidth x y≤(fieldWidth x y)^2 := by nlinarith
  unfold window
  nlinarith

theorem five_windows (x y : Rat) :
    window x.num.natAbs y.num.natAbs≤524320*(fieldWidth x y)^2 ∧
    window x.den y.den≤524320*(fieldWidth x y)^2 ∧
    window (productMagnitude x y) (productDenominator x y)≤524320*(fieldWidth x y)^2 ∧
    window (productMagnitude x y) (normalizer x y)≤524320*(fieldWidth x y)^2 ∧
    window (productDenominator x y) (normalizer x y)≤524320*(fieldWidth x y)^2 := by
  obtain ⟨ha,hb,hc,hd,he⟩ := five_scales x y
  exact ⟨window_bound x y _ _ ha,window_bound x y _ _ hb,window_bound x y _ _ hc,
    window_bound x y _ _ hd,window_bound x y _ _ he⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048
