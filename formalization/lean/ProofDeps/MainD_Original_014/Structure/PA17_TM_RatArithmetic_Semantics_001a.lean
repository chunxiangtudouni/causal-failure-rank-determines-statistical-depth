module
public import PaperProofs.Common.RationalControllerComputation
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-! Pure normalization facts for the exact original rational encoding.
The gcd below is a mathematical description of a runtime result, never
an oracle or a claimed already-verified gcd machine. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001

def normMag (n : Int) (d : Nat) : Nat :=
  if d = 0 then 0 else n.natAbs / Nat.gcd n.natAbs d

def normDen (n : Int) (d : Nat) : Nat :=
  if d = 0 then 1 else d / Nat.gcd n.natAbs d

def normNeg (n : Int) (d : Nat) : Bool := decide (d ≠ 0 ∧ n < 0)

theorem normalized_mag (n : Int) (d : Nat) : (mkRat n d).num.natAbs = normMag n d := by
  by_cases hd : d = 0
  · simp [hd,normMag]
  · rw [Rat.num_mkRat,ite_eq_right hd,Nat.gcd_comm]
    have dvd : (Nat.gcd n.natAbs d : Int) ∣ n :=
      Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left n.natAbs d)
    rw [Int.natAbs_ediv_of_dvd dvd,Int.natAbs_natCast]
    exact (ite_eq_right hd).symm

theorem normalized_den (n : Int) (d : Nat) : (mkRat n d).den = normDen n d := by
  rw [Rat.den_mkRat]
  simp only [normDen,Nat.gcd_comm]

theorem normalized_neg (n : Int) (d : Nat) : decide (mkRat n d < 0) = normNeg n d := by
  by_cases hd : d = 0
  · simp [hd,normNeg]
  · simp [normNeg,hd,Rat.mkRat_neg_iff n hd]

theorem normalization_data (n : Int) (d : Nat) :
    (mkRat n d).num.natAbs = normMag n d ∧ (mkRat n d).den = normDen n d ∧
      decide (mkRat n d < 0) = normNeg n d :=
  ⟨normalized_mag n d,normalized_den n d,normalized_neg n d⟩

theorem normalization_den_positive (n : Int) (d : Nat) : 0 < normDen n d := by
  rw [← normalized_den]
  exact (mkRat n d).den_pos

theorem normalization_coprime (n : Int) (d : Nat) : Nat.Coprime (normMag n d) (normDen n d) := by
  rw [← normalized_mag,← normalized_den]
  exact (mkRat n d).reduced

theorem zero_denominator (n : Int) :
    mkRat n 0 = 0 ∧ normMag n 0 = 0 ∧ normDen n 0 = 1 ∧ normNeg n 0 = false := by
  simp [normMag,normDen,normNeg]

theorem zero_numerator (d : Nat) :
    normMag 0 d = 0 ∧ normDen 0 d = 1 ∧ normNeg 0 d = false := by
  rw [← normalized_mag,← normalized_den,← normalized_neg]
  simp

theorem rational_datum_normalized (n : Int) (d : Nat) :
    encodeDatum (.rational (mkRat n d)) =
      [true,normNeg n d] ++ encodeNat (normMag n d) ++ encodeNat (normDen n d) := by
  rw [encodeDatum,normalized_mag,normalized_den,normalized_neg]

theorem rational_output_normalized (n : Int) (d : Nat) :
    encode [.rational (mkRat n d)] =
      encodeNat 1 ++ ([true,normNeg n d] ++ encodeNat (normMag n d) ++ encodeNat (normDen n d)) ++ [true] := by
  simp only [encode,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    rational_datum_normalized]

theorem rational_pair_encoding (x y : Rat) :
    encode [.rational x,.rational y] =
      encodeNat 2 ++ (encodeDatum (.rational x) ++ encodeDatum (.rational y)) ++ [true] := by
  simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSemantics001
