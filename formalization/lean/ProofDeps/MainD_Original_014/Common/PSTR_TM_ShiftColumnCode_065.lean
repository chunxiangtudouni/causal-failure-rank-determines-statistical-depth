module
public import Common.PSTR_TM_CompareCode_054

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMShiftColumnCode065
open PaperProofs.Common.Native.RationalControllerComputation

/-- B1's resident A is doubled while resident B and every archive cell
are retained. Overflow is a computed finite-control result at actual EOF. -/
def shiftPairs : Bool → List (Bool × Bool) → List (Bool × Bool)
  | _, [] => []
  | carry, (a,b) :: later => (carry,b) :: shiftPairs a later

def finalCarry : Bool → List (Bool × Bool) → Bool
  | carry, [] => carry
  | _, (a,_) :: later => finalCarry a later

def readA (carry : Bool) : Fin 20 := if carry then 1 else 0
def flagA (carry a : Bool) : Fin 20 := ⟨2 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def writeA (carry a : Bool) : Fin 20 := ⟨6 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def advance (phase : Fin 4) (carry : Bool) : Fin 20 :=
  ⟨10 + 2 * phase.val + carry.toNat, by have hp := phase.isLt; have hc := Bool.toNat_le carry; omega⟩
def haltLabel (carry : Bool) : Fin 20 := if carry then 19 else 18

/-- Exactly20 fixed ordinary Bool labels. Every digit move/write and the
owned00 EOF check is real. No width/overflow/answer field is read as input. -/
def shiftMachine : Machine 19 := fun q symbol =>
  if q.val < 2 then some (flagA (decide (q.val = 1)) symbol, .move .right)
  else if q.val < 6 then
    let carry := decide (4 ≤ q.val)
    let a := decide (q.val % 2 = 1)
    if symbol then some (writeA carry a, .move .left) else some (haltLabel carry, .move .left)
  else if q.val < 10 then
    let carry := decide (8 ≤ q.val)
    let a := decide (q.val % 2 = 1)
    some (advance 0 a, .write carry)
  else if q.val < 18 then
    let carry := decide (q.val % 2 = 1)
    match (q.val - 10) / 2 with
    | 0 => some (advance 1 carry, .move .right)
    | 1 => some (advance 2 carry, .move .right)
    | 2 => some (advance 3 carry, .move .right)
    | _ => some (readA carry, .move .right)
  else none

def state (q : Fin 20) (left right : List Bool) : MachineState 19 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem shift_halt (carry : Bool) (left right : List Bool) :
    Turing.TM0.step shiftMachine (state (haltLabel carry) left right) = none := by
  cases carry <;> simp [Turing.TM0.step, shiftMachine, state, haltLabel]

theorem shiftPairs_length (carry : Bool) (pairs : List (Bool × Bool)) :
    (shiftPairs carry pairs).length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [shiftPairs, List.length_cons, ih]

theorem secondValue_shiftPairs (carry : Bool) (pairs : List (Bool × Bool)) :
    PSTRTMBinaryAdd024.secondValue (shiftPairs carry pairs) = PSTRTMBinaryAdd024.secondValue pairs := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit b (PSTRTMBinaryAdd024.secondValue (shiftPairs a later)) =
      Nat.bit b (PSTRTMBinaryAdd024.secondValue later)
    rw [ih]

theorem firstValue_shiftPairs (carry : Bool) (pairs : List (Bool × Bool)) :
    PSTRTMBinaryAdd024.firstValue (shiftPairs carry pairs) + 2^pairs.length * (finalCarry carry pairs).toNat =
      2 * PSTRTMBinaryAdd024.firstValue pairs + carry.toNat := by
  induction pairs generalizing carry with
  | nil => cases carry <;> rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have ht := ih a
    change Nat.bit carry (PSTRTMBinaryAdd024.firstValue (shiftPairs a later)) +
      2^(later.length+1) * (finalCarry a later).toNat =
      2 * Nat.bit a (PSTRTMBinaryAdd024.firstValue later) + carry.toNat
    cases carry <;> cases a <;>
      simp only [Nat.bit, Bool.cond_false, Bool.cond_true, Nat.pow_succ, Bool.toNat_false, Bool.toNat_true] at ht ⊢ <;>
      nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMShiftColumnCode065
