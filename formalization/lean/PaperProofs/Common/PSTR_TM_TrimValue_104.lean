module
public import PaperProofs.Common.PSTR_TM_TrimCode_103

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimValue104
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 PSTRTMIncrement009

theorem append_high_zero (digits : List Bool) : valueDigits (digits++[false])=valueDigits digits := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change Nat.bit bit (valueDigits (later++[false]))=Nat.bit bit (valueDigits later)
    rw [ih]

theorem keep_value (reversed : List Bool) : valueDigits (keepReverse reversed).reverse=valueDigits reversed.reverse := by
  induction reversed with
  | nil => rfl
  | cons bit earlier ih =>
    cases bit with
    | false => simpa only [keepReverse,List.reverse_cons,append_high_zero] using ih
    | true => rfl

theorem keep_head (reversed : List Bool) (h : keepReverse reversed≠[]) : (keepReverse reversed).head?=some true := by
  induction reversed with
  | nil => exact False.elim (h rfl)
  | cons bit earlier ih =>
    cases bit with
    | false => exact ih h
    | true => rfl

theorem trimmed_value (digits : List Bool) : valueDigits (trimmed digits)=valueDigits digits := by
  have hv := keep_value digits.reverse
  rw [List.reverse_reverse] at hv
  cases hk : keepReverse digits.reverse with
  | nil =>
    simpa [trimmed,hk,valueDigits,Nat.bit] using hv
  | cons first later =>
    simpa only [trimmed,hk] using hv

/-- Value equality becomes EXACT original canonical payload only after
the real high-zero eraser has stopped on a true high digit or written one
false digit for zero. This is the semantic obligation consumed by its
actual trimmer trace; it is not a free replacement of tape contents. -/
theorem trimmed_canonical (digits : List Bool) : trimmed digits=PSTRTMNatValue017.rawPayload (valueDigits digits) := by
  cases hk : keepReverse digits.reverse with
  | nil =>
    have hv := trimmed_value digits
    have hz : valueDigits digits=0 := by simpa [trimmed,hk,valueDigits,Nat.bit] using hv.symm
    calc
      trimmed digits = [false] := by simp only [trimmed,hk]
      _ = PSTRTMNatValue017.rawPayload 0 := rfl
      _ = PSTRTMNatValue017.rawPayload (valueDigits digits) := congrArg PSTRTMNatValue017.rawPayload hz.symm
  | cons first later =>
    have hn : keepReverse digits.reverse≠[] := by intro h; rw [hk] at h; cases h
    have hh := keep_head digits.reverse hn
    rw [hk] at hh
    have he : first=true := Option.some.inj hh
    subst first
    have hlast : (trimmed digits).getLast?=some true := by
      simp only [trimmed,hk,List.reverse_cons,List.getLast?_append,List.getLast?_singleton,Option.some_or]
    have hc := PSTRTMCanonical020.canonical_digits (trimmed digits) hlast
    rw [trimmed_value] at hc
    exact hc

theorem keep_length_le (reversed : List Bool) : (keepReverse reversed).length ≤ reversed.length := by
  induction reversed with
  | nil => rfl
  | cons bit earlier ih => cases bit <;> simp only [keepReverse,List.length_cons] <;> omega

theorem trimmed_length_le (digits : List Bool) : (trimmed digits).length ≤ digits.length+1 := by
  have hk := keep_length_le digits.reverse
  rw [List.length_reverse] at hk
  cases h : keepReverse digits.reverse with
  | nil => simp only [trimmed,h,List.length_cons,List.length_nil]; omega
  | cons first later =>
    simp only [h,List.length_cons] at hk
    simp only [trimmed,h,List.length_reverse,List.length_cons]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimValue104
