module
public import Common.PSTR_TM_Increment_009

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMBinaryAdd024
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009

/-- Actual adjacent operand bits and their two true flag cells. Width
alignment is an INTERNAL transport obligation, not an original input promise. -/
def operandColumns (pairs : List (Bool × Bool)) : List Bool :=
  pairs.flatMap (fun pair => [pair.1, true, pair.2, true])

theorem operandColumns_length (pairs : List (Bool × Bool)) :
    (operandColumns pairs).length = 4 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    change (operandColumns later).length + 4 = 4 * (later.length + 1)
    rw [ih]
    omega

def resultColumns (digits : List Bool) : List Bool :=
  digits.flatMap (fun bit => [bit, true, false, true])

def leftResults (previous : List Bool) : List Bool :=
  previous.flatMap (fun bit => [true, false, true, bit])

def sumBit (carry a b : Bool) : Bool := Bool.xor (Bool.xor a b) carry
def carryBit (carry a b : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

def sumDigits : Bool → List (Bool × Bool) → List Bool
  | carry, [] => if carry then [true] else []
  | carry, (a, b) :: later => sumBit carry a b :: sumDigits (carryBit carry a b) later

def firstValue (pairs : List (Bool × Bool)) : Nat := valueDigits (pairs.map Prod.fst)
def secondValue (pairs : List (Bool × Bool)) : Nat := valueDigits (pairs.map Prod.snd)

theorem bit_sum (carry a b : Bool) (x y : Nat) :
    Nat.bit (sumBit carry a b) (x + y + (carryBit carry a b).toNat) =
      Nat.bit a x + Nat.bit b y + carry.toNat := by
  cases carry <;> cases a <;> cases b <;> simp [sumBit, carryBit, Nat.bit] <;> omega

/-- Exact arithmetic of the SAME finite carry truth table used by the code.
No iteration is by the numerical operand value. -/
theorem sumDigits_value (carry : Bool) (pairs : List (Bool × Bool)) :
    valueDigits (sumDigits carry pairs) = firstValue pairs + secondValue pairs + carry.toNat := by
  induction pairs generalizing carry with
  | nil => cases carry <;> rfl
  | cons pair later ih =>
    obtain ⟨a, b⟩ := pair
    simp only [sumDigits, valueDigits, ih, firstValue, secondValue, List.map_cons]
    exact bit_sum carry a b _ _

def carryState (carry : Bool) : Fin 50 := if carry then 1 else 0
def flagState (carry a : Bool) : Fin 50 := ⟨2 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def readBState (carry a : Bool) : Fin 50 := ⟨6 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def backState (carry a b : Bool) : Fin 50 :=
  ⟨10 + 4 * carry.toNat + 2 * a.toNat + b.toNat, by cases carry <;> cases a <;> cases b <;> decide⟩
def writeState (carry a b : Bool) : Fin 50 :=
  ⟨18 + 4 * carry.toNat + 2 * a.toNat + b.toNat, by cases carry <;> cases a <;> cases b <;> decide⟩
def advanceState (phase : Fin 5) (carry : Bool) : Fin 50 :=
  ⟨26 + 2 * phase.val + carry.toNat, by have h := phase.isLt; cases carry <;> dsimp <;> omega⟩

/-- Uniform50-label ordinary Bool adder. Carries are fixed finite control;
every iteration reads one aligned column, writes its sum and clears B. After
the final carry extension it really rewinds by the true flag cells. -/
def addMachine : Machine 49 := fun q symbol =>
  if q.val < 2 then
    some (flagState (decide (q.val = 1)) symbol, .move .right)
  else if q.val < 6 then
    let carry := decide (4 ≤ q.val)
    let a := decide (q.val % 2 = 1)
    if symbol then some (readBState carry a, .move .right)
    else if a then none else some (if carry then 41 else 36, .move .left)
  else if q.val < 10 then
    some (backState (decide (8 ≤ q.val)) (decide (q.val % 2 = 1)) symbol, .move .left)
  else if q.val < 18 then
    some (writeState (decide (14 ≤ q.val)) (decide ((q.val - 10) % 4 ≥ 2)) (decide (q.val % 2 = 1)), .move .left)
  else if q.val < 26 then
    let carry := decide (22 ≤ q.val)
    let a := decide ((q.val - 18) % 4 ≥ 2)
    let b := decide (q.val % 2 = 1)
    some (advanceState 0 (carryBit carry a b), .write (sumBit carry a b))
  else if q.val < 36 then
    let carry := decide (q.val % 2 = 1)
    match (q.val - 26) / 2 with
    | 0 => some (advanceState 1 carry, .move .right)
    | 1 => some (advanceState 2 carry, .move .right)
    | 2 => some (advanceState 3 carry, .write false)
    | 3 => some (advanceState 4 carry, .move .right)
    | _ => some (carryState carry, .move .right)
  else
    match q.val with
    | 36 => some (37, .move .left)
    | 37 => some (if symbol then 38 else 43, if symbol then .move .left else .move .right)
    | 38 => some (39, .move .left)
    | 39 => some (40, .move .left)
    | 40 => some (37, .move .left)
    | 41 => some (42, .write true)
    | 42 => some (44, .move .right)
    | 44 => some (45, .write true)
    | 45 => some (46, .move .right)
    | 46 => some (47, .write false)
    | 47 => some (48, .move .right)
    | 48 => some (49, .write true)
    | 49 => some (36, .move .right)
    | _ => none

def state (q : Fin 50) (left right : List Bool) : MachineState 49 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem add_halt (left right : List Bool) :
    Turing.TM0.step addMachine (state 43 left right) = none := by
  simp [Turing.TM0.step, addMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMBinaryAdd024
