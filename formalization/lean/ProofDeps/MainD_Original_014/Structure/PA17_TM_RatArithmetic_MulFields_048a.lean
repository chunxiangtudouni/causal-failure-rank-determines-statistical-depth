module
public import Structure.PA17_TM_RatArithmetic_Semantics_001e
public import Structure.PA17_TM_RatArithmetic_Parse_002e
public import Structure.PA17_TM_RatArithmetic_Sign_003c

/-! Interpret the real five-call multiplication pipeline. The equalities
below are poststate contracts, never supplied original input answers.
No zero sensor or sign controller execution is asserted by pure semantics. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048

open PA17TMRatArithmeticSemantics001 PA17TMRatArithmeticParse002

def productMagnitude (x y : Rat) : Nat := x.num.natAbs*y.num.natAbs
def productDenominator (x y : Rat) : Nat := x.den*y.den
def normalizer (x y : Rat) : Nat := Nat.gcd (productMagnitude x y) (productDenominator x y)
def quotientNumerator (x y : Rat) : Nat := productMagnitude x y/normalizer x y
def quotientDenominator (x y : Rat) : Nat := productDenominator x y/normalizer x y
def zeroRepairedSign (sx sy : Bool) (u : Nat) : Bool := if u=0 then false else Bool.xor sx sy

theorem productDenominator_pos (x y : Rat) : 0<productDenominator x y :=
  Nat.mul_pos x.den_pos y.den_pos

/-- Each M/D/G/U/V equality is supplied by its actual earlier native run.
The repair expression specifies what the later REAL U-zero/control port must
do; it is not a claim that a sensor has already run. -/
theorem actual_fields (x y : Rat) (m d g u v : Nat)
    (hm : m=x.num.natAbs*y.num.natAbs) (hd : d=x.den*y.den)
    (hg : g=Nat.gcd m d) (hu : u=m/g) (hv : v=d/g) :
    u=(x*y).num.natAbs ∧ v=(x*y).den ∧
      zeroRepairedSign (sign x) (sign y) u=sign (x*y) := by
  have value : mkRat (signed (xorNegative x y) m) d=x*y := by
    rw [hm,hd]
    exact mul_signed_value x y
  have hd0 : d≠0 := by
    rw [hd]
    exact Nat.ne_of_gt (Nat.mul_pos x.den_pos y.den_pos)
  obtain ⟨hn,hden,hs⟩ := quotient_result_fields (xorNegative x y) m d g u v
    (decide (u=0)) false (x*y) value hg hu hv rfl (by simp [hd0])
  refine ⟨?_,?_,?_⟩
  · simpa only [resultMagnitude,Bool.false_eq_true,ite_false] using hn.symm
  · simpa only [resultDenominator,Bool.false_eq_true,ite_false] using hden.symm
  · have repair : zeroRepairedSign (sign x) (sign y) u=
        repairedSign (xorNegative x y) (decide (u=0)) false := by
      by_cases hz : u=0 <;> simp [zeroRepairedSign,repairedSign,xorNegative,sign,hz]
    exact repair.trans hs.symm

theorem pipeline_fields (x y : Rat) :
    quotientNumerator x y=(x*y).num.natAbs ∧ quotientDenominator x y=(x*y).den ∧
      zeroRepairedSign (sign x) (sign y) (quotientNumerator x y)=sign (x*y) :=
  actual_fields x y (productMagnitude x y) (productDenominator x y) (normalizer x y)
    (quotientNumerator x y) (quotientDenominator x y) rfl rfl rfl rfl rfl

theorem pipeline_zero_iff (x y : Rat) : quotientNumerator x y=0 ↔ x=0 ∨ y=0 := by
  rw [(pipeline_fields x y).1,PA17TMRatArithmeticSign003.numerator_zero_iff,mul_eq_zero]

theorem pipeline_zero_left (y : Rat) :
    quotientNumerator 0 y=0 ∧ quotientDenominator 0 y=1 ∧
      zeroRepairedSign (sign 0) (sign y) (quotientNumerator 0 y)=false := by
  simpa only [zero_mul,Rat.num_zero,Int.natAbs_zero,Rat.den_zero,sign,lt_self_iff_false,decide_false] using pipeline_fields 0 y

theorem pipeline_zero_right (x : Rat) :
    quotientNumerator x 0=0 ∧ quotientDenominator x 0=1 ∧
      zeroRepairedSign (sign x) (sign 0) (quotientNumerator x 0)=false := by
  simpa only [mul_zero,Rat.num_zero,Int.natAbs_zero,Rat.den_zero,sign,lt_self_iff_false,decide_false] using pipeline_fields x 0

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048
