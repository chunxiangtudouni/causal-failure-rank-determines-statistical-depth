module
public import Structure.PA17_TM_RatArithmetic_Semantics_001d

/-! Interpretation of REAL internal gcd/division results. The g/u/v and zero
flags below are poststate values with proved machine contracts, never extra
original inputs or supplied answers. Denominator zero is repaired to0/1. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001

def resultMagnitude (zeroDenominator : Bool) (quotient : Nat) : Nat :=
  if zeroDenominator then 0 else quotient

def resultDenominator (zeroDenominator : Bool) (quotient : Nat) : Nat :=
  if zeroDenominator then 1 else quotient

def repairedSign (negative zeroQuotient zeroDenominator : Bool) : Bool :=
  negative && !zeroQuotient && !zeroDenominator

/-- The assembler may test the ACTUAL quotient for zero, rather than retain
the raw numerator's zero flag through the gcd and two division calls. -/
theorem quotient_repaired_sign (negative : Bool) (magnitude denominator g quotient : Nat)
    (zeroQuotient zeroDenominator : Bool) (hg : g = Nat.gcd magnitude denominator)
    (hq : quotient = magnitude/g) (hzq : zeroQuotient = decide (quotient = 0))
    (hzd : zeroDenominator = decide (denominator = 0)) :
    repairedSign negative zeroQuotient zeroDenominator = canonicalNegative negative magnitude denominator := by
  rw [hzq,hzd]
  by_cases hd : denominator = 0
  · simp [repairedSign,canonicalNegative,hd]
  · by_cases hzero : quotient = 0
    · have hm : normMag (signed negative magnitude) denominator = 0 := by
        rw [signed_normalization_mag,ite_eq_right hd,← hg,← hq,hzero]
      have hn := (canonical_zero_from_magnitude (signed negative magnitude) denominator hm).2
      have hc : canonicalNegative negative magnitude denominator = false := by
        change decide (denominator ≠ 0 ∧ negative = true ∧ magnitude ≠ 0) = false
        exact (signed_normalization_sign negative magnitude denominator).symm.trans hn
      rw [hc]
      simp [repairedSign,hzero]
    · have hm : magnitude ≠ 0 := by
        intro hm0
        apply hzero
        rw [hq,hm0]
        simp
      cases negative <;> simp [repairedSign,canonicalNegative,hd,hzero,hm]

theorem quotient_result_fields (negative : Bool) (magnitude denominator g numeratorQuotient denominatorQuotient : Nat)
    (zeroNumerator zeroDenominator : Bool) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q)
    (hg : g = Nat.gcd magnitude denominator)
    (hn : numeratorQuotient = magnitude/g) (hd : denominatorQuotient = denominator/g)
    (hzn : zeroNumerator = decide (numeratorQuotient = 0))
    (hzd : zeroDenominator = decide (denominator = 0)) :
    q.num.natAbs = resultMagnitude zeroDenominator numeratorQuotient ∧
    q.den = resultDenominator zeroDenominator denominatorQuotient ∧
    decide (q < 0) = repairedSign negative zeroNumerator zeroDenominator := by
  obtain ⟨hm,he,hs⟩ := signed_candidate_fields negative magnitude denominator q value
  have hmag : resultMagnitude zeroDenominator numeratorQuotient = canonicalMagnitude magnitude denominator := by
    rw [hzd,hn,hg]
    by_cases hz : denominator = 0 <;> simp [resultMagnitude,canonicalMagnitude,hz]
  have hden : resultDenominator zeroDenominator denominatorQuotient = canonicalDenominator magnitude denominator := by
    rw [hzd,hd,hg]
    by_cases hz : denominator = 0 <;> simp [resultDenominator,canonicalDenominator,hz]
  exact ⟨hm.trans hmag.symm,he.trans hden.symm,
    hs.trans (quotient_repaired_sign negative magnitude denominator g numeratorQuotient
      zeroNumerator zeroDenominator hg hn hzn hzd).symm⟩

theorem quotient_result_datum (negative : Bool) (magnitude denominator g numeratorQuotient denominatorQuotient : Nat)
    (zeroNumerator zeroDenominator : Bool) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q)
    (hg : g = Nat.gcd magnitude denominator)
    (hn : numeratorQuotient = magnitude/g) (hd : denominatorQuotient = denominator/g)
    (hzn : zeroNumerator = decide (numeratorQuotient = 0))
    (hzd : zeroDenominator = decide (denominator = 0)) :
    encodeDatum (.rational q) =
      [true,repairedSign negative zeroNumerator zeroDenominator] ++
        encodeNat (resultMagnitude zeroDenominator numeratorQuotient) ++
        encodeNat (resultDenominator zeroDenominator denominatorQuotient) := by
  obtain ⟨hm,he,hs⟩ := quotient_result_fields negative magnitude denominator g numeratorQuotient denominatorQuotient
    zeroNumerator zeroDenominator q value hg hn hd hzn hzd
  simp only [encodeDatum,hm,he,hs]

theorem quotient_result_output (negative : Bool) (magnitude denominator g numeratorQuotient denominatorQuotient : Nat)
    (zeroNumerator zeroDenominator : Bool) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q)
    (hg : g = Nat.gcd magnitude denominator)
    (hn : numeratorQuotient = magnitude/g) (hd : denominatorQuotient = denominator/g)
    (hzn : zeroNumerator = decide (numeratorQuotient = 0))
    (hzd : zeroDenominator = decide (denominator = 0)) :
    encode [.rational q] = encodeNat 1 ++
      ([true,repairedSign negative zeroNumerator zeroDenominator] ++
        encodeNat (resultMagnitude zeroDenominator numeratorQuotient) ++
        encodeNat (resultDenominator zeroDenominator denominatorQuotient)) ++ [true] := by
  simp only [encode,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [quotient_result_datum negative magnitude denominator g numeratorQuotient denominatorQuotient
    zeroNumerator zeroDenominator q value hg hn hd hzn hzd]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001
