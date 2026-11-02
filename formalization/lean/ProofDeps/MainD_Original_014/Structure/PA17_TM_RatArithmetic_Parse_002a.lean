module
public import Common.PSTR_TM_Length_004
public import Common.PSTR_TM_NatValue_017

/-! Exact original two-Rat input. These are encoding identities and field
facts, not an alternate input, supplied parser output or arithmetic oracle. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def sign (x : Rat) : Bool := decide (x < 0)

def numeratorDigits (x : Rat) : List Bool := PSTRTMNatValue017.rawPayload x.num.natAbs

def denominatorDigits (x : Rat) : List Bool := PSTRTMNatValue017.rawPayload x.den

def rawField (digits : List Bool) : List Bool :=
  List.replicate digits.length true ++ false::digits

theorem encodeNat_rawField (n : Nat) :
    encodeNat n = rawField (PSTRTMNatValue017.rawPayload n) := by
  simp only [encodeNat,rawField,PSTRTMNatValue017.rawPayload,List.length_ofFn,
    List.append_assoc,List.singleton_append]

theorem rational_datum (x : Rat) :
    encodeDatum (.rational x) = [true,sign x] ++
      rawField (numeratorDigits x) ++ rawField (denominatorDigits x) := by
  rw [encodeDatum,encodeNat_rawField,encodeNat_rawField]
  rfl

theorem original_pair (x y : Rat) :
    encode [.rational x,.rational y] =
      encodeNat 2 ++ ([true,sign x] ++ rawField (numeratorDigits x) ++ rawField (denominatorDigits x)) ++
        ([true,sign y] ++ rawField (numeratorDigits y) ++ rawField (denominatorDigits y)) ++ [true] := by
  simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    rational_datum,List.append_nil,List.append_assoc]

theorem encodeNat_two : encodeNat 2 = [true,true,false,false,true] := by decide

theorem rawField_length (digits : List Bool) : (rawField digits).length = 2*digits.length+1 := by
  simp only [rawField,List.length_append,List.length_replicate,List.length_cons]
  omega

theorem numeratorDigits_length (x : Rat) : (numeratorDigits x).length = natBits x.num.natAbs := by
  simp only [numeratorDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem denominatorDigits_length (x : Rat) : (denominatorDigits x).length = natBits x.den := by
  simp only [denominatorDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem numeratorDigits_value (x : Rat) :
    PSTRTMIncrement009.valueDigits (numeratorDigits x) = x.num.natAbs :=
  PSTRTMNatValue017.valueDigits_rawPayload x.num.natAbs

theorem denominatorDigits_value (x : Rat) :
    PSTRTMIncrement009.valueDigits (denominatorDigits x) = x.den :=
  PSTRTMNatValue017.valueDigits_rawPayload x.den

theorem denominator_positive (x : Rat) : 0 < x.den := x.den_pos

theorem numerator_denominator_coprime (x : Rat) : Nat.Coprime x.num.natAbs x.den := x.reduced

theorem datum_length (x : Rat) :
    (encodeDatum (.rational x)).length =
      2*((numeratorDigits x).length+(denominatorDigits x).length)+4 := by
  rw [numeratorDigits_length,denominatorDigits_length]
  exact PSTRTMLength004.encodeDatum_rational_length x

theorem pair_length (x y : Rat) :
    (encode [.rational x,.rational y]).length =
      2*((numeratorDigits x).length+(denominatorDigits x).length+
        (numeratorDigits y).length+(denominatorDigits y).length)+14 := by
  rw [original_pair,encodeNat_two]
  simp only [List.length_append,List.length_cons,List.length_nil,rawField_length]
  omega

theorem field_widths_positive (x : Rat) :
    1 ≤ (numeratorDigits x).length ∧ 1 ≤ (denominatorDigits x).length := by
  rw [numeratorDigits_length,denominatorDigits_length]
  simp only [natBits]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
