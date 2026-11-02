module

public import RootL01_SymbolicSource_Unary_Run_021

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.Unary

open PaperProofs.Common.Native
open RationalControllerComputation

theorem evaluate_append (front back : List Bool) (amount : Nat) :
    evaluate (front++back) amount = evaluate back (evaluate front amount) := by
  induction front generalizing amount with
  | nil => rfl
  | cons bit front ih => exact ih (2*amount+bitValue bit)

theorem evaluate_reverse (digits : List Bool) :
    evaluate digits.reverse 0 = PSTRTMIncrement009.valueDigits digits := by
  induction digits with
  | nil => rfl
  | cons bit digits ih =>
    rw [List.reverse_cons,evaluate_append,ih]
    cases bit <;> rfl

theorem evaluate_canonical (value : Nat) :
    evaluate (PSTRTMNatValue017.rawPayload value).reverse 0 = value :=
  (evaluate_reverse _).trans (PSTRTMNatValue017.valueDigits_rawPayload value)

theorem canonical_time_le (value : Nat) :
    time (PSTRTMNatValue017.rawPayload value).reverse 0 ≤
      (3*value+3)*(PSTRTMNatValue017.rawPayload value).length+2 := by
  simpa only [evaluate_canonical,List.length_reverse] using
    time_le (PSTRTMNatValue017.rawPayload value).reverse 0

end RootL01.SymbolicSource.Unary
