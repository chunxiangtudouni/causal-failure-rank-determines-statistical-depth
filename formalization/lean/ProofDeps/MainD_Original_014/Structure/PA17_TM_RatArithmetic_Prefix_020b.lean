module
public import Structure.PA17_TM_RatArithmetic_Prefix_020a
public import Structure.PA17_TM_RatArithmetic_Semantics_001e
public import Structure.PA17_TM_RatArithmetic_Sign_003b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix020

open PA17TMRatArithmeticSemantics001

theorem prefix_canonical_word (q : Rat) :
    prefixWord (decide (q<0)) (encodeNat q.num.natAbs++encodeNat q.den++[true]) =
      encode [.rational q] := by
  simp only [encode,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    encodeDatum,PA17TMRatArithmeticSign003.encodeNat_one,prefixWord,
    List.cons_append,List.nil_append,List.append_assoc]

/-- Only the physical final encoding stage. Its entry fields/port must be
produced by the genuine arithmetic, zero guard, and two-field encoder. -/
theorem quotient_prefix_runsFrom (negative : Bool)
    (magnitude denominator g numeratorQuotient denominatorQuotient : Nat)
    (zeroNumerator zeroDenominator : Bool) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator=q)
    (hg : g=Nat.gcd magnitude denominator)
    (hn : numeratorQuotient=magnitude/g) (hd : denominatorQuotient=denominator/g)
    (hzn : zeroNumerator=decide (numeratorQuotient=0))
    (hzd : zeroDenominator=decide (denominator=0))
    (a b c d e : Bool) (archive : List Bool) :
    PSTRTMSeq005.RunsFrom prefixMachine
      (prefixState (repairedSign negative zeroNumerator zeroDenominator) 0
        (a::b::c::d::e::archive)
        (encodeNat (resultMagnitude zeroDenominator numeratorQuotient)++
          encodeNat (resultDenominator zeroDenominator denominatorQuotient)++[true]))
      (prefixTrace (repairedSign negative zeroNumerator zeroDenominator) a b c d e archive
        (encodeNat (resultMagnitude zeroDenominator numeratorQuotient)++
          encodeNat (resultDenominator zeroDenominator denominatorQuotient)++[true]))
      (prefixState (repairedSign negative zeroNumerator zeroDenominator) 10 archive (encode [.rational q])) := by
  obtain ⟨hm,he,hs⟩ := quotient_result_fields negative magnitude denominator g
    numeratorQuotient denominatorQuotient zeroNumerator zeroDenominator q value hg hn hd hzn hzd
  have hw : prefixWord (repairedSign negative zeroNumerator zeroDenominator)
      (encodeNat (resultMagnitude zeroDenominator numeratorQuotient)++
        encodeNat (resultDenominator zeroDenominator denominatorQuotient)++[true]) =
        encode [.rational q] := by
    rw [←hm,←he,←hs]
    exact prefix_canonical_word q
  have run := prefix_runsFrom (repairedSign negative zeroNumerator zeroDenominator) a b c d e archive
    (encodeNat (resultMagnitude zeroDenominator numeratorQuotient)++
      encodeNat (resultDenominator zeroDenominator denominatorQuotient)++[true])
  rw [hw] at run
  exact run

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPrefix020
