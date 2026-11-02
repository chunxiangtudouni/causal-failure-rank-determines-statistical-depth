module
public import Structure.PA17_TM_RatArithmetic_Semantics_001c

/-! Natural cross-products and signed difference are enough for all four
operations. The final gcd normalization and canonical sign repair are exact
original Datum encodings, including zero and division by zero. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001

def crossLeft (x y : Rat) : Nat := x.num.natAbs*y.den
def crossRight (x y : Rat) : Nat := y.num.natAbs*x.den
def addMagnitude (x y : Rat) : Nat := sumMag (decide (x<0)) (decide (y<0)) (crossLeft x y) (crossRight x y)
def addNegative (x y : Rat) : Bool := sumSign (decide (x<0)) (decide (y<0)) (crossLeft x y) (crossRight x y)
def subMagnitude (x y : Rat) : Nat := sumMag (decide (x<0)) (!decide (y<0)) (crossLeft x y) (crossRight x y)
def subNegative (x y : Rat) : Bool := sumSign (decide (x<0)) (!decide (y<0)) (crossLeft x y) (crossRight x y)
def xorNegative (x y : Rat) : Bool := Bool.xor (decide (x<0)) (decide (y<0))
def divMagnitude (x y : Rat) : Nat := if y.num.natAbs = 0 then 0 else x.num.natAbs*y.den

theorem signed_add_candidate (x y : Rat) : signed (addNegative x y) (addMagnitude x y) = addNum x y := by
  simp only [addNegative,addMagnitude,signed_addition,crossLeft,crossRight,signed_scale,signed_rat_num,addNum]

theorem signed_sub_candidate (x y : Rat) : signed (subNegative x y) (subMagnitude x y) = subNum x y := by
  simp only [subNegative,subMagnitude,signed_addition,crossLeft,crossRight,signed_scale,signed_flip,
    signed_rat_num,subNum,sub_eq_add_neg,neg_mul]

theorem signed_mul_candidate (x y : Rat) :
    signed (xorNegative x y) (x.num.natAbs*y.num.natAbs) = mulNum x y := by
  simp only [xorNegative,signed_multiply,signed_rat_num,mulNum]

theorem signed_div_candidate (x y : Rat) : signed (xorNegative x y) (divMagnitude x y) = divNum x y := by
  by_cases hy : y.num = 0
  · simp [divMagnitude,hy,signed,divNum]
  · have habs : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
    have hsign : signed (decide (y<0)) y.den = y.num.sign*(y.den : Int) := by
      have hs := signed_scale (intSign y.num) 1 y.den
      rw [Nat.one_mul,signed_one_sign y.num hy] at hs
      simpa only [rat_num_sign] using hs
    simp only [divMagnitude,ite_eq_right habs,xorNegative,signed_multiply,signed_rat_num,hsign,divNum]

theorem signed_candidate_encoding (negative : Bool) (magnitude denominator : Nat) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q) :
    encode [.rational q] = encodeNat 1 ++
      ([true,decide (denominator ≠ 0 ∧ negative = true ∧ magnitude ≠ 0)] ++
        encodeNat (if denominator = 0 then 0 else magnitude / Nat.gcd magnitude denominator) ++
        encodeNat (if denominator = 0 then 1 else denominator / Nat.gcd magnitude denominator)) ++ [true] := by
  rw [← value]
  simpa only [signed_normalization_sign,signed_normalization_mag,signed_normalization_den] using
    rational_output_normalized (signed negative magnitude) denominator

theorem add_signed_value (x y : Rat) :
    mkRat (signed (addNegative x y) (addMagnitude x y)) (productDen x y) = x+y := by
  rw [signed_add_candidate,add_value]

theorem sub_signed_value (x y : Rat) :
    mkRat (signed (subNegative x y) (subMagnitude x y)) (productDen x y) = x-y := by
  rw [signed_sub_candidate,sub_value]

theorem mul_signed_value (x y : Rat) :
    mkRat (signed (xorNegative x y) (x.num.natAbs*y.num.natAbs)) (productDen x y) = x*y := by
  rw [signed_mul_candidate,mul_value]

theorem div_signed_value (x y : Rat) :
    mkRat (signed (xorNegative x y) (divMagnitude x y)) (quotientDen x y) = x/y := by
  rw [signed_div_candidate,div_value]

/- The following functions specify the three fields to be produced by the
   runtime gcd/division/sign-repair path. They assert no runtime capability. -/
def canonicalMagnitude (magnitude denominator : Nat) : Nat :=
  if denominator = 0 then 0 else magnitude / Nat.gcd magnitude denominator

def canonicalDenominator (magnitude denominator : Nat) : Nat :=
  if denominator = 0 then 1 else denominator / Nat.gcd magnitude denominator

def canonicalNegative (negative : Bool) (magnitude denominator : Nat) : Bool :=
  decide (denominator ≠ 0 ∧ negative = true ∧ magnitude ≠ 0)

def canonicalDatum (negative : Bool) (magnitude denominator : Nat) : List Bool :=
  [true,canonicalNegative negative magnitude denominator] ++
    encodeNat (canonicalMagnitude magnitude denominator) ++
    encodeNat (canonicalDenominator magnitude denominator)

theorem signed_candidate_fields (negative : Bool) (magnitude denominator : Nat) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q) :
    q.num.natAbs = canonicalMagnitude magnitude denominator ∧
    q.den = canonicalDenominator magnitude denominator ∧
    decide (q < 0) = canonicalNegative negative magnitude denominator := by
  rw [← value]
  simpa only [signed_normalization_mag,signed_normalization_den,signed_normalization_sign,
    canonicalMagnitude,canonicalDenominator,canonicalNegative] using
    normalization_data (signed negative magnitude) denominator

theorem signed_candidate_datum (negative : Bool) (magnitude denominator : Nat) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q) :
    encodeDatum (.rational q) = canonicalDatum negative magnitude denominator := by
  obtain ⟨hm,hd,hs⟩ := signed_candidate_fields negative magnitude denominator q value
  simp only [encodeDatum,canonicalDatum,hm,hd,hs]

theorem signed_candidate_output (negative : Bool) (magnitude denominator : Nat) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q) :
    encode [.rational q] = encodeNat 1 ++ canonicalDatum negative magnitude denominator ++ [true] := by
  simpa only [canonicalDatum,canonicalMagnitude,canonicalDenominator,canonicalNegative] using
    signed_candidate_encoding negative magnitude denominator q value

theorem add_signed_fields (x y : Rat) :
    (x+y).num.natAbs = canonicalMagnitude (addMagnitude x y) (productDen x y) ∧
    (x+y).den = canonicalDenominator (addMagnitude x y) (productDen x y) ∧
    decide (x+y < 0) = canonicalNegative (addNegative x y) (addMagnitude x y) (productDen x y) :=
  signed_candidate_fields _ _ _ _ (add_signed_value x y)

theorem sub_signed_fields (x y : Rat) :
    (x-y).num.natAbs = canonicalMagnitude (subMagnitude x y) (productDen x y) ∧
    (x-y).den = canonicalDenominator (subMagnitude x y) (productDen x y) ∧
    decide (x-y < 0) = canonicalNegative (subNegative x y) (subMagnitude x y) (productDen x y) :=
  signed_candidate_fields _ _ _ _ (sub_signed_value x y)

theorem mul_signed_fields (x y : Rat) :
    (x*y).num.natAbs = canonicalMagnitude (x.num.natAbs*y.num.natAbs) (productDen x y) ∧
    (x*y).den = canonicalDenominator (x.num.natAbs*y.num.natAbs) (productDen x y) ∧
    decide (x*y < 0) = canonicalNegative (xorNegative x y) (x.num.natAbs*y.num.natAbs) (productDen x y) :=
  signed_candidate_fields _ _ _ _ (mul_signed_value x y)

theorem div_signed_fields (x y : Rat) :
    (x/y).num.natAbs = canonicalMagnitude (divMagnitude x y) (quotientDen x y) ∧
    (x/y).den = canonicalDenominator (divMagnitude x y) (quotientDen x y) ∧
    decide (x/y < 0) = canonicalNegative (xorNegative x y) (divMagnitude x y) (quotientDen x y) :=
  signed_candidate_fields _ _ _ _ (div_signed_value x y)

theorem add_signed_output (x y : Rat) :
    encode [.rational (x+y)] = encodeNat 1 ++
      canonicalDatum (addNegative x y) (addMagnitude x y) (productDen x y) ++ [true] :=
  signed_candidate_output _ _ _ _ (add_signed_value x y)

theorem sub_signed_output (x y : Rat) :
    encode [.rational (x-y)] = encodeNat 1 ++
      canonicalDatum (subNegative x y) (subMagnitude x y) (productDen x y) ++ [true] :=
  signed_candidate_output _ _ _ _ (sub_signed_value x y)

theorem mul_signed_output (x y : Rat) :
    encode [.rational (x*y)] = encodeNat 1 ++
      canonicalDatum (xorNegative x y) (x.num.natAbs*y.num.natAbs) (productDen x y) ++ [true] :=
  signed_candidate_output _ _ _ _ (mul_signed_value x y)

theorem div_signed_output (x y : Rat) :
    encode [.rational (x/y)] = encodeNat 1 ++
      canonicalDatum (xorNegative x y) (divMagnitude x y) (quotientDen x y) ++ [true] :=
  signed_candidate_output _ _ _ _ (div_signed_value x y)

theorem div_zero_canonical_fields (x : Rat) :
    canonicalMagnitude (divMagnitude x 0) (quotientDen x 0) = 0 ∧
    canonicalDenominator (divMagnitude x 0) (quotientDen x 0) = 1 ∧
    canonicalNegative (xorNegative x 0) (divMagnitude x 0) (quotientDen x 0) = false := by
  simp [canonicalMagnitude,canonicalDenominator,canonicalNegative,quotientDen]

theorem div_zero_canonical_output (x : Rat) :
    encode [.rational (x/0)] = encodeNat 1 ++
      ([true,false] ++ encodeNat 0 ++ encodeNat 1) ++ [true] := by
  simpa [normMag,normDen,normNeg] using rational_output_normalized 0 1

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001
