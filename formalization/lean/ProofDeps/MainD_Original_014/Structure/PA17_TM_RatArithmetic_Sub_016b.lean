module
public import Structure.PA17_TM_RatArithmetic_Sub_016a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
open PSTRTMBinaryAdd024 PA17TMDivisionSub001

theorem zero_map_first (pairs : List Pair) : firstValue (pairs.map zeroPair) = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    change Nat.bit false (firstValue (pairs.map zeroPair)) = 0
    rw [ih]
    rfl

theorem saturatedPairs_length (pairs : List Pair) : (saturatedPairs pairs).length = pairs.length := by
  unfold saturatedPairs
  split <;> simp only [List.length_map,afterSub,subPairs_length]

/-- The two real HALT labels encode the arithmetic underflow test. There is
no non-underflow qualification on the original inputs. -/
theorem saturated_value (pairs : List Pair) :
    firstValue (saturatedPairs pairs) = firstValue pairs-secondValue pairs := by
  cases hb : borrow pairs with
  | false =>
    have hf : finalBorrow false pairs = false := hb
    have hge : secondValue pairs ≤ firstValue pairs := by
      simpa only [Bool.toNat_false,Nat.add_zero] using (finalBorrow_eq_false_iff false pairs).mp hf
    simpa [saturatedPairs,hb,afterSub] using
      (subtraction_exact pairs hge).2
  | true =>
    have hnot : ¬secondValue pairs ≤ firstValue pairs := by
      intro hge
      have hf := (subtraction_exact pairs hge).1
      change borrow pairs = false at hf
      rw [hb] at hf
      cases hf
    have hz : firstValue pairs-secondValue pairs = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [saturatedPairs,hb,zero_map_first,hz]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
