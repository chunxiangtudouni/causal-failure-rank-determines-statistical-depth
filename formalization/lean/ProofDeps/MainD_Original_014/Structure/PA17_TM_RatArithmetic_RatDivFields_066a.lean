module
public import Structure.PA17_TM_RatArithmetic_MulFields_048b
public import Structure.PA17_TM_RatArithmetic_WideCache_045b

/-! Pure interpretation of the actual division call graph. M is the genuine
Nx*Dy even when Ny=0; neither the native gcd nor its two quotient results is
silently replaced. The real D-zero branch must produce 0/1/false. These
poststate equalities and size bounds assert no sensor or machine execution. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivFields066

open PA17TMRatArithmeticSemantics001 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticNativeSize007 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticWideCache045 PSTRTMArithmetic008 PSTRTMLength004 PSTRTMNatValue017

def divMagnitude (x y : Rat) : Nat := x.num.natAbs*y.den
def divDenominator (x y : Rat) : Nat := x.den*y.num.natAbs
def divNormalizer (x y : Rat) : Nat := Nat.gcd (divMagnitude x y) (divDenominator x y)
def divNumerator (x y : Rat) : Nat := divMagnitude x y/divNormalizer x y
def divReducedDenominator (x y : Rat) : Nat := divDenominator x y/divNormalizer x y

theorem divDenominator_zero_iff (x y : Rat) : divDenominator x y=0 ↔ y=0 :=
  quotientDen_zero_iff x y

/-- Unlike the older candidate, the actual M is not cleared before a D-zero
branch. A zero denominator still makes this signed rational exactly zero. -/
theorem signed_value (x y : Rat) :
    mkRat (signed (xorNegative x y) (divMagnitude x y)) (divDenominator x y)=x/y := by
  by_cases hy : y.num.natAbs=0
  · have hy0 : y=0 := by simpa only [Int.natAbs_eq_zero,Rat.num_eq_zero] using hy
    subst y
    simp [divDenominator]
  · simpa only [PA17TMRatArithmeticSemantics001.divMagnitude,ite_eq_right hy,
      divMagnitude,divDenominator,quotientDen] using div_signed_value x y

/-- The five natural equalities are obtained from the actual native calls.
The result guards specify the work of the actual later branch controller. -/
theorem actual_fields (x y : Rat) (m d g u v : Nat)
    (hm : m=x.num.natAbs*y.den) (hd : d=x.den*y.num.natAbs)
    (hg : g=Nat.gcd m d) (hu : u=m/g) (hv : v=d/g) :
    resultMagnitude (decide (d=0)) u=(x/y).num.natAbs ∧
    resultDenominator (decide (d=0)) v=(x/y).den ∧
    repairedSign (xorNegative x y) (decide (u=0)) (decide (d=0))=sign (x/y) := by
  have value : mkRat (signed (xorNegative x y) m) d=x/y := by
    rw [hm,hd]
    exact signed_value x y
  obtain ⟨hn,he,hs⟩ := quotient_result_fields (xorNegative x y) m d g u v
    (decide (u=0)) (decide (d=0)) (x/y) value hg hu hv rfl rfl
  exact ⟨hn.symm,he.symm,hs.symm⟩

theorem pipeline_fields (x y : Rat) :
    resultMagnitude (decide (divDenominator x y=0)) (divNumerator x y)=(x/y).num.natAbs ∧
    resultDenominator (decide (divDenominator x y=0)) (divReducedDenominator x y)=(x/y).den ∧
    repairedSign (xorNegative x y) (decide (divNumerator x y=0))
      (decide (divDenominator x y=0))=sign (x/y) :=
  actual_fields x y (divMagnitude x y) (divDenominator x y) (divNormalizer x y)
    (divNumerator x y) (divReducedDenominator x y) rfl rfl rfl rfl rfl

/-- D nonzero is only an internal fact established by the real observed
branch. It is never a qualification on the original two rational inputs. -/
theorem normal_fields (x y : Rat) (hd : divDenominator x y≠0) :
    divNumerator x y=(x/y).num.natAbs ∧
    divReducedDenominator x y=(x/y).den ∧
    PA17TMRatArithmeticMulFields048.zeroRepairedSign (sign x) (sign y)
      (divNumerator x y)=sign (x/y) := by
  obtain ⟨hn,he,hs⟩ := pipeline_fields x y
  have repair : PA17TMRatArithmeticMulFields048.zeroRepairedSign (sign x) (sign y)
      (divNumerator x y)=repairedSign (xorNegative x y)
        (decide (divNumerator x y=0)) (decide (divDenominator x y=0)) := by
    by_cases hz : divNumerator x y=0 <;>
      simp [PA17TMRatArithmeticMulFields048.zeroRepairedSign,repairedSign,
        xorNegative,sign,hd,hz]
  exact ⟨by simpa [resultMagnitude,hd] using hn,
    by simpa [resultDenominator,hd] using he,
    repair.trans hs⟩

theorem normal_actual_fields (x y : Rat) (m d g u v : Nat)
    (hm : m=x.num.natAbs*y.den) (hd : d=x.den*y.num.natAbs)
    (hg : g=Nat.gcd m d) (hu : u=m/g) (hv : v=d/g) (hd0 : d≠0) :
    u=(x/y).num.natAbs ∧ v=(x/y).den ∧
    PA17TMRatArithmeticMulFields048.zeroRepairedSign (sign x) (sign y) u=sign (x/y) := by
  have hn := normal_fields x y (by simpa only [divDenominator,←hd] using hd0)
  rw [hu,hv,hg,hm,hd]
  exact hn

theorem observed_denominator_zero (x y : Rat) (d : Nat) (zeroD : Bool)
    (hd : d=x.den*y.num.natAbs) (hzd : zeroD=decide (d=0)) :
    zeroD=decide (y=0) := by
  rw [hzd,hd]
  change decide (divDenominator x y=0)=decide (y=0)
  simp only [divDenominator_zero_iff]

theorem zero_denominator_fields (x y : Rat) (hd : divDenominator x y=0) :
    resultMagnitude (decide (divDenominator x y=0)) (divNumerator x y)=0 ∧
    resultDenominator (decide (divDenominator x y=0)) (divReducedDenominator x y)=1 ∧
    repairedSign (xorNegative x y) (decide (divNumerator x y=0))
      (decide (divDenominator x y=0))=false := by
  simp [resultMagnitude,resultDenominator,repairedSign,hd]

theorem zero_numerator_sign (x y : Rat) (hu : divNumerator x y=0) :
    repairedSign (xorNegative x y) (decide (divNumerator x y=0))
      (decide (divDenominator x y=0))=false := by
  simp [repairedSign,hu]

theorem division_by_zero_fields (x : Rat) :
    resultMagnitude (decide (divDenominator x 0=0)) (divNumerator x 0)=0 ∧
    resultDenominator (decide (divDenominator x 0=0)) (divReducedDenominator x 0)=1 ∧
    repairedSign (xorNegative x 0) (decide (divNumerator x 0=0))
      (decide (divDenominator x 0=0))=false :=
  zero_denominator_fields x 0 ((divDenominator_zero_iff x 0).2 rfl)

theorem zero_branch_canonical (x y : Rat) (hd : divDenominator x y=0) :
    (x/y).num.natAbs=0 ∧ (x/y).den=1 ∧ sign (x/y)=false := by
  have hy : y=0 := (divDenominator_zero_iff x y).1 hd
  subst y
  simp [sign]

theorem numerator_zero_canonical (x y : Rat) (hd : divDenominator x y≠0)
    (hu : divNumerator x y=0) : (x/y).num.natAbs=0 ∧ (x/y).den=1 ∧ sign (x/y)=false := by
  have hn : (x/y).num.natAbs=0 := (normal_fields x y hd).1.symm.trans hu
  have hq : x/y=0 := (PA17TMRatArithmeticSign003.numerator_zero_iff (x/y)).mp hn
  simp [hq,sign]

/-- Observed flags are constrained poststate metadata, not original inputs.
This lemma does not assert that either physical sensor has already run. -/
theorem actual_observed_fields (x y : Rat) (m d g u v : Nat) (zeroU zeroD : Bool)
    (hm : m=x.num.natAbs*y.den) (hd : d=x.den*y.num.natAbs)
    (hg : g=Nat.gcd m d) (hu : u=m/g) (hv : v=d/g)
    (hzu : zeroU=decide (u=0)) (hzd : zeroD=decide (d=0)) :
    resultMagnitude zeroD u=(x/y).num.natAbs ∧
    resultDenominator zeroD v=(x/y).den ∧
    repairedSign (xorNegative x y) zeroU zeroD=sign (x/y) := by
  rw [hzu,hzd]
  exact actual_fields x y m d g u v hm hd hg hu hv

theorem pipeline_output (x y : Rat) :
    encode [.rational (x/y)]=encodeNat 1 ++
      ([true,repairedSign (xorNegative x y) (decide (divNumerator x y=0))
        (decide (divDenominator x y=0))] ++
        encodeNat (resultMagnitude (decide (divDenominator x y=0)) (divNumerator x y)) ++
        encodeNat (resultDenominator (decide (divDenominator x y=0))
          (divReducedDenominator x y))) ++ [true] :=
  quotient_result_output (xorNegative x y) (divMagnitude x y) (divDenominator x y)
    (divNormalizer x y) (divNumerator x y) (divReducedDenominator x y)
    (decide (divNumerator x y=0)) (decide (divDenominator x y=0)) (x/y)
    (signed_value x y) rfl rfl rfl rfl rfl

theorem zero_denominator_output (x y : Rat) (hd : divDenominator x y=0) :
    encode [.rational (x/y)]=encodeNat 1 ++
      ([true,false] ++ encodeNat 0 ++ encodeNat 1) ++ [true] := by
  rw [pipeline_output]
  simp only [hd,decide_true,resultMagnitude,resultDenominator,repairedSign,
    Bool.not_true,Bool.and_false,ite_true]

/- All size statements below are total, including D=0, G=0 and native a/0.
The physical D-zero path may skip gcd and division; no native-domain premise
is hidden in these bounds. All widths refer to the exact original codec. -/

theorem divMagnitude_bits (x y : Rat) : natBits (divMagnitude x y)≤fieldWidth x y := by
  have hb := crossLeft_bits_le x y
  have he := PA17TMRatArithmeticMulFields048.inputBits_eq_fieldWidth x y
  change natBits (divMagnitude x y)≤_ at hb
  unfold inputBits at he
  omega

theorem divDenominator_bits (x y : Rat) : natBits (divDenominator x y)≤fieldWidth x y := by
  simpa only [divDenominator,quotientDen,
    PA17TMRatArithmeticMulFields048.inputBits_eq_fieldWidth] using quotientDen_bits_le x y

theorem divNormalizer_bits (x y : Rat) : natBits (divNormalizer x y)≤fieldWidth x y := by
  by_cases hd : divDenominator x y=0
  · simpa [divNormalizer,hd] using divMagnitude_bits x y
  · have hg := natBits_mono (Nat.gcd_le_right (divMagnitude x y) (Nat.pos_of_ne_zero hd))
    exact hg.trans (divDenominator_bits x y)

theorem div_quotient_bits (x y : Rat) :
    natBits (divNumerator x y)≤fieldWidth x y ∧
    natBits (divReducedDenominator x y)≤fieldWidth x y :=
  ⟨(natBits_mono (Nat.div_le_self _ _)).trans (divMagnitude_bits x y),
    (natBits_mono (Nat.div_le_self _ _)).trans (divDenominator_bits x y)⟩

theorem all_field_bits (x y : Rat) :
    natBits (divMagnitude x y)≤fieldWidth x y ∧
    natBits (divDenominator x y)≤fieldWidth x y ∧
    natBits (divNormalizer x y)≤fieldWidth x y ∧
    natBits (divNumerator x y)≤fieldWidth x y ∧
    natBits (divReducedDenominator x y)≤fieldWidth x y :=
  ⟨divMagnitude_bits x y,divDenominator_bits x y,divNormalizer_bits x y,
    (div_quotient_bits x y).1,(div_quotient_bits x y).2⟩

theorem canonical_field_bits (x y : Rat) :
    natBits (x/y).num.natAbs≤fieldWidth x y ∧ natBits (x/y).den≤fieldWidth x y := by
  simpa only [PA17TMRatArithmeticMulFields048.inputBits_eq_fieldWidth] using
    div_normalized_bits_le x y

theorem five_scales (x y : Rat) :
    scale x.num.natAbs y.den≤4*fieldWidth x y ∧
    scale x.den y.num.natAbs≤4*fieldWidth x y ∧
    scale (divMagnitude x y) (divDenominator x y)≤4*fieldWidth x y ∧
    scale (divMagnitude x y) (divNormalizer x y)≤4*fieldWidth x y ∧
    scale (divDenominator x y) (divNormalizer x y)≤4*fieldWidth x y := by
  obtain ⟨hnx,hny,hdx,hdy⟩ := PA17TMRatArithmeticMulFields048.original_field_bits x y
  have hw : 1≤fieldWidth x y := by
    have h := PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y
    omega
  have hm := divMagnitude_bits x y
  have hd := divDenominator_bits x y
  have hg := divNormalizer_bits x y
  exact ⟨PA17TMRatArithmeticMulFields048.scale_le_four_width _ _ _ hw hnx hdy,
    PA17TMRatArithmeticMulFields048.scale_le_four_width _ _ _ hw hdx hny,
    PA17TMRatArithmeticMulFields048.scale_le_four_width _ _ _ hw hm hd,
    PA17TMRatArithmeticMulFields048.scale_le_four_width _ _ _ hw hm hg,
    PA17TMRatArithmeticMulFields048.scale_le_four_width _ _ _ hw hd hg⟩

theorem five_windows (x y : Rat) :
    window x.num.natAbs y.den≤allocationK*(fieldWidth x y)^2 ∧
    window x.den y.num.natAbs≤allocationK*(fieldWidth x y)^2 ∧
    window (divMagnitude x y) (divDenominator x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (divMagnitude x y) (divNormalizer x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (divDenominator x y) (divNormalizer x y)≤allocationK*(fieldWidth x y)^2 := by
  obtain ⟨ha,hb,hc,hd,he⟩ := five_scales x y
  have hw : 1≤fieldWidth x y := by
    have h := PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y
    omega
  exact ⟨window_le_allocated _ _ _ hw ha,window_le_allocated _ _ _ hw hb,
    window_le_allocated _ _ _ hw hc,window_le_allocated _ _ _ hw hd,
    window_le_allocated _ _ _ hw he⟩

theorem actual_five_scales (x y : Rat) (m d g : Nat)
    (hm : m=x.num.natAbs*y.den) (hd : d=x.den*y.num.natAbs) (hg : g=Nat.gcd m d) :
    scale x.num.natAbs y.den≤4*fieldWidth x y ∧
    scale x.den y.num.natAbs≤4*fieldWidth x y ∧ scale m d≤4*fieldWidth x y ∧
    scale m g≤4*fieldWidth x y ∧ scale d g≤4*fieldWidth x y := by
  rw [hg,hm,hd]
  exact five_scales x y

theorem payload_widths (x y : Rat) :
    (rawPayload (divMagnitude x y)).length≤fieldWidth x y ∧
    (rawPayload (divDenominator x y)).length≤fieldWidth x y ∧
    (rawPayload (divNormalizer x y)).length≤fieldWidth x y ∧
    (rawPayload (divNumerator x y)).length≤fieldWidth x y ∧
    (rawPayload (divReducedDenominator x y)).length≤fieldWidth x y := by
  simpa only [rawPayload,List.length_ofFn] using all_field_bits x y

theorem output_length_le (x y : Rat) :
    (encode [.rational (x/y)]).length≤2*(encode [.rational x,.rational y]).length :=
  div_output_length_le x y

def inputPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def nativeTimeCoefficient : Nat := 1048576
def nativeSpaceCoefficient : Nat := 2097154

theorem native_coefficients_pos : 0<nativeTimeCoefficient ∧ 0<nativeSpaceCoefficient := by
  decide

/-- Arithmetic rescaling of the frozen native-cache time and every-prefix
space constants only. The actual callee supplies its own single Runs trace. -/
theorem native_budget_le (x y : Rat) (a b : Nat) (hs : scale a b≤4*fieldWidth x y) :
    65536*(scale a b)^2≤nativeTimeCoefficient*inputPower x y ∧
    (encode [.rational x,.rational y]).length+131072*(scale a b)^2+1≤
      nativeSpaceCoefficient*inputPower x y := by
  let i := (encode [.rational x,.rational y]).length
  have hw : fieldWidth x y ≤ i + 1 := by
    have hp := pair_length x y
    change i=2*fieldWidth x y+14 at hp
    omega
  have hscale : scale a b≤4*(i+1) := hs.trans (Nat.mul_le_mul_left 4 hw)
  have hsq := Nat.pow_le_pow_left hscale 2
  have hp : (i+1)^2≤(i+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hi : i≤(i+1)^4 := by
    have hlin : i+1≤(i+1)^2 := by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (i+1) (show 1 ≤ i + 1 by omega)
    omega
  have hsquare : (scale a b)^2≤16*(i+1)^4 := by nlinarith only [hsq,hp]
  have hpositive : 1≤(i+1)^4 := Nat.succ_le_of_lt (by positivity : 0<(i+1)^4)
  change 65536*(scale a b)^2≤1048576*(i+1)^4 ∧
    i+131072*(scale a b)^2+1≤2097154*(i+1)^4
  constructor <;> omega

theorem five_native_budgets (x y : Rat) :
    65536*(scale x.num.natAbs y.den)^2≤nativeTimeCoefficient*inputPower x y ∧
    65536*(scale x.den y.num.natAbs)^2≤nativeTimeCoefficient*inputPower x y ∧
    65536*(scale (divMagnitude x y) (divDenominator x y))^2≤nativeTimeCoefficient*inputPower x y ∧
    65536*(scale (divMagnitude x y) (divNormalizer x y))^2≤nativeTimeCoefficient*inputPower x y ∧
    65536*(scale (divDenominator x y) (divNormalizer x y))^2≤nativeTimeCoefficient*inputPower x y := by
  obtain ⟨ha,hb,hc,hd,he⟩ := five_scales x y
  exact ⟨(native_budget_le x y _ _ ha).1,(native_budget_le x y _ _ hb).1,
    (native_budget_le x y _ _ hc).1,(native_budget_le x y _ _ hd).1,
    (native_budget_le x y _ _ he).1⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivFields066
