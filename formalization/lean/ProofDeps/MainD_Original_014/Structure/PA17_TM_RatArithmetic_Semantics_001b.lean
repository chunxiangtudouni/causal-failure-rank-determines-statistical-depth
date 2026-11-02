module
public import Structure.PA17_TM_RatArithmetic_Semantics_001a

/-! The four unnormalized cross-products. These describe natural-number
runtime operations, not final answers supplied to an arithmetic machine. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001

def addNum (x y : Rat) : Int := x.num*y.den+y.num*x.den
def subNum (x y : Rat) : Int := x.num*y.den-y.num*x.den
def mulNum (x y : Rat) : Int := x.num*y.num
def productDen (x y : Rat) : Nat := x.den*y.den
def divNum (x y : Rat) : Int := x.num*(y.num.sign*y.den)
def quotientDen (x y : Rat) : Nat := x.den*y.num.natAbs

theorem add_value (x y : Rat) : mkRat (addNum x y) (productDen x y) = x+y :=
  (Rat.add_def' x y).symm

theorem sub_value (x y : Rat) : mkRat (subNum x y) (productDen x y) = x-y :=
  (Rat.sub_def' x y).symm

theorem mul_value (x y : Rat) : mkRat (mulNum x y) (productDen x y) = x*y :=
  (Rat.mul_eq_mkRat x y).symm

theorem div_value (x y : Rat) : mkRat (divNum x y) (quotientDen x y) = x/y := by
  by_cases hy : y.num = 0
  · have hy0 : y = 0 := Rat.num_eq_zero.mp hy
    simp [hy0,quotientDen]
  · rw [div_eq_mul_inv,Rat.mul_eq_mkRat,Rat.num_inv,Rat.den_inv,ite_eq_right hy]
    rfl

theorem productDen_positive (x y : Rat) : 0 < productDen x y :=
  Nat.mul_pos x.den_pos y.den_pos

theorem quotientDen_zero_iff (x y : Rat) : quotientDen x y = 0 ↔ y = 0 := by
  simp [quotientDen,x.den_nz,Rat.num_eq_zero]

theorem add_normalized (x y : Rat) :
    (x+y).num.natAbs = normMag (addNum x y) (productDen x y) ∧
      (x+y).den = normDen (addNum x y) (productDen x y) ∧
      decide (x+y < 0) = normNeg (addNum x y) (productDen x y) := by
  simpa only [add_value] using normalization_data (addNum x y) (productDen x y)

theorem sub_normalized (x y : Rat) :
    (x-y).num.natAbs = normMag (subNum x y) (productDen x y) ∧
      (x-y).den = normDen (subNum x y) (productDen x y) ∧
      decide (x-y < 0) = normNeg (subNum x y) (productDen x y) := by
  simpa only [sub_value] using normalization_data (subNum x y) (productDen x y)

theorem mul_normalized (x y : Rat) :
    (x*y).num.natAbs = normMag (mulNum x y) (productDen x y) ∧
      (x*y).den = normDen (mulNum x y) (productDen x y) ∧
      decide (x*y < 0) = normNeg (mulNum x y) (productDen x y) := by
  simpa only [mul_value] using normalization_data (mulNum x y) (productDen x y)

theorem div_normalized (x y : Rat) :
    (x/y).num.natAbs = normMag (divNum x y) (quotientDen x y) ∧
      (x/y).den = normDen (divNum x y) (quotientDen x y) ∧
      decide (x/y < 0) = normNeg (divNum x y) (quotientDen x y) := by
  simpa only [div_value] using normalization_data (divNum x y) (quotientDen x y)

theorem add_output (x y : Rat) :
    encode [.rational (x+y)] = encodeNat 1 ++
      ([true,normNeg (addNum x y) (productDen x y)] ++
        encodeNat (normMag (addNum x y) (productDen x y)) ++
        encodeNat (normDen (addNum x y) (productDen x y))) ++ [true] := by
  rw [← add_value]
  exact rational_output_normalized _ _

theorem sub_output (x y : Rat) :
    encode [.rational (x-y)] = encodeNat 1 ++
      ([true,normNeg (subNum x y) (productDen x y)] ++
        encodeNat (normMag (subNum x y) (productDen x y)) ++
        encodeNat (normDen (subNum x y) (productDen x y))) ++ [true] := by
  rw [← sub_value]
  exact rational_output_normalized _ _

theorem mul_output (x y : Rat) :
    encode [.rational (x*y)] = encodeNat 1 ++
      ([true,normNeg (mulNum x y) (productDen x y)] ++
        encodeNat (normMag (mulNum x y) (productDen x y)) ++
        encodeNat (normDen (mulNum x y) (productDen x y))) ++ [true] := by
  rw [← mul_value]
  exact rational_output_normalized _ _

theorem div_output (x y : Rat) :
    encode [.rational (x/y)] = encodeNat 1 ++
      ([true,normNeg (divNum x y) (quotientDen x y)] ++
        encodeNat (normMag (divNum x y) (quotientDen x y)) ++
        encodeNat (normDen (divNum x y) (quotientDen x y))) ++ [true] := by
  rw [← div_value]
  exact rational_output_normalized _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001
