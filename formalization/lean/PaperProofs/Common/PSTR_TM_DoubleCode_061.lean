module
public import PaperProofs.Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMDoubleCode061
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMNatValue017

/-- Internal result shape. The SINGLE false digit representing zero is
retained. Otherwise a real low zero digit is inserted before the payload. -/
def doubleDigits (digits : List Bool) : List Bool :=
  if digits = [false] then digits else false :: digits

/-- Fixed14-label doubling guard. It reads at most two actual flagged
digits to distinguish canonical zero. The positive branch really allocates
two cells to the left and writes01; the zero branch really rewinds. -/
def doubleMachine : Machine 13 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 6 else 1, if symbol then .move .left else .move .right)
  | 1 => some (2, .move .right)
  | 2 => some (if symbol then 3 else 4, if symbol then .move .left else .move .right)
  | 3 => some (5, .move .left)
  | 4 => some (if symbol then 8 else 11, .move .left)
  | 5 => some (6, .move .left)
  | 6 => some (7, .write true)
  | 7 => some (9, .move .left)
  | 8 => some (3, .move .left)
  | 9 => some (10, .write false)
  | 11 => some (12, .move .left)
  | 12 => some (13, .move .left)
  | 13 => some (10, .write symbol)
  | _ => none

def state (q : Fin 14) (left right : List Bool) : MachineState 13 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem double_halt (left right : List Bool) : Turing.TM0.step doubleMachine (state 10 left right) = none := by
  simp [Turing.TM0.step, doubleMachine, state]

theorem rawPayload_ne_nil (value : Nat) : rawPayload value ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [rawPayload, List.length_ofFn, List.length_nil, natBits] at hl
  omega

theorem doubleDigits_rawPayload (value : Nat) : doubleDigits (rawPayload value) = rawPayload (2 * value) := by
  by_cases hn : value = 0
  · subst value
    rfl
  · have he : rawPayload value ≠ [false] := by
      intro h
      have hv := valueDigits_rawPayload value
      rw [h] at hv
      have hz : value = 0 := hv.symm
      exact hn hz
    rw [doubleDigits, ite_eq_right he]
    have ht : (false :: rawPayload value).getLast? = some true := by
      rw [List.getLast?_cons_of_ne_nil (rawPayload_ne_nil value)]
      exact PSTRTMCanonical020.rawPayload_last value hn
    have hc := PSTRTMCanonical020.canonical_digits (false :: rawPayload value) ht
    simpa only [valueDigits, valueDigits_rawPayload, Nat.bit_false] using hc

theorem doubleDigits_length_le (digits : List Bool) : (doubleDigits digits).length ≤ digits.length + 1 := by
  unfold doubleDigits
  split <;> simp

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMDoubleCode061
