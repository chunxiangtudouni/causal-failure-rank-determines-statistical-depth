module
public import Structure.PA17_TM_RatArithmetic_Semantics_001b

/-! A sign/magnitude arithmetic bridge. Sign decisions and natural
comparison/subtraction branches describe work for the actual machine,
not caller-supplied quotient, gcd, answer or correctness certificates. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001

def signed (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(magnitude : Int) else magnitude

def intSign (n : Int) : Bool := decide (n < 0)

theorem signed_int_abs (n : Int) : signed (intSign n) n.natAbs = n := by
  by_cases hn : n < 0
  · have ha := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hn)
    simp [signed,intSign,hn,ha]
  · have hn0 : 0 ≤ n := by omega
    have ha := Int.natAbs_of_nonneg hn0
    simp [signed,intSign,hn,ha]

theorem signed_abs (negative : Bool) (magnitude : Nat) :
    (signed negative magnitude).natAbs = magnitude := by
  cases negative <;> simp [signed]

theorem signed_flip (negative : Bool) (magnitude : Nat) :
    signed (!negative) magnitude = -(signed negative magnitude) := by
  cases negative <;> simp [signed]

theorem signed_negative (negative : Bool) (magnitude : Nat) :
    signed negative magnitude < 0 ↔ negative = true ∧ magnitude ≠ 0 := by
  cases negative <;> simp [signed]
  exact Nat.pos_iff_ne_zero

theorem rat_num_sign (q : Rat) : intSign q.num = decide (q < 0) := by
  have he : (q.num < 0) ↔ q < 0 := by
    simpa only [not_le] using not_congr (Rat.num_nonneg (q := q))
  simp only [intSign,he]

theorem signed_rat_num (q : Rat) : signed (decide (q < 0)) q.num.natAbs = q.num := by
  rw [← rat_num_sign]
  exact signed_int_abs q.num

theorem signed_one_sign (n : Int) (hn : n ≠ 0) : signed (intSign n) 1 = n.sign := by
  by_cases hneg : n < 0
  · simp [signed,intSign,hneg,Int.sign_eq_neg_one_of_neg hneg]
  · have hpos : 0 < n := by omega
    simp [signed,intSign,hneg,Int.sign_eq_one_of_pos hpos]

theorem signed_scale (negative : Bool) (magnitude scale : Nat) :
    signed negative (magnitude*scale) = signed negative magnitude * (scale : Int) := by
  cases negative <;> simp [signed]

theorem signed_multiply (sx sy : Bool) (a b : Nat) :
    signed (Bool.xor sx sy) (a*b) = signed sx a * signed sy b := by
  cases sx <;> cases sy <;> simp [signed]

def sumMag (sx sy : Bool) (a b : Nat) : Nat :=
  if sx = sy then a+b else if a < b then b-a else a-b

def sumSign (sx sy : Bool) (a b : Nat) : Bool :=
  if sx = sy then sx else if a < b then sy else sx

/-- The opposite-sign branch uses one actual magnitude comparison and
one natural subtraction; either equality case is permitted before zero repair. -/
theorem signed_addition (sx sy : Bool) (a b : Nat) :
    signed (sumSign sx sy a b) (sumMag sx sy a b) = signed sx a + signed sy b := by
  cases sx <;> cases sy <;> by_cases hab : a < b <;>
    simp_all [sumSign,sumMag,signed] <;> omega

theorem signed_normalization_mag (negative : Bool) (magnitude denominator : Nat) :
    normMag (signed negative magnitude) denominator =
      if denominator = 0 then 0 else magnitude / Nat.gcd magnitude denominator := by
  simp only [normMag,signed_abs]

theorem signed_normalization_den (negative : Bool) (magnitude denominator : Nat) :
    normDen (signed negative magnitude) denominator =
      if denominator = 0 then 1 else denominator / Nat.gcd magnitude denominator := by
  simp only [normDen,signed_abs]

theorem signed_normalization_sign (negative : Bool) (magnitude denominator : Nat) :
    normNeg (signed negative magnitude) denominator =
      decide (denominator ≠ 0 ∧ negative = true ∧ magnitude ≠ 0) := by
  simp only [normNeg,signed_negative]

theorem normalization_gcd_positive (n : Int) (d : Nat) (hd : d ≠ 0) :
    0 < Nat.gcd n.natAbs d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hd)

theorem canonical_zero_from_magnitude (n : Int) (d : Nat) (hz : normMag n d = 0) :
    normDen n d = 1 ∧ normNeg n d = false := by
  have hq : mkRat n d = 0 := by
    rw [← normalized_mag] at hz
    simpa only [Int.natAbs_eq_zero,Rat.num_eq_zero] using hz
  rw [← normalized_den,← normalized_neg,hq]
  simp

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001
