module
public import Common.PSTR_TM_CompareTrace_055

/-! Fixed finite-control resident binary subtraction. The width is read
from actual flag cells and the owned00 terminator, never from host fuel. -/
@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
open PSTRTMBinaryAdd024 PSTRTMIncrement009

def differenceBit (borrow a b : Bool) : Bool := Bool.xor (Bool.xor a b) borrow
def borrowBit (borrow a b : Bool) : Bool := ((!a) && (b || borrow)) || (b && borrow)

def subPairs : Bool → List (Bool × Bool) → List (Bool × Bool)
  | _, [] => []
  | borrow, (a,b) :: later => (differenceBit borrow a b,b) :: subPairs (borrowBit borrow a b) later

def finalBorrow : Bool → List (Bool × Bool) → Bool
  | borrow, [] => borrow
  | borrow, (a,b) :: later => finalBorrow (borrowBit borrow a b) later

def readA (borrow : Bool) : Fin 28 := if borrow then 1 else 0
def flagA (borrow a : Bool) : Fin 28 :=
  ⟨2 + 2 * borrow.toNat + a.toNat, by cases borrow <;> cases a <;> decide⟩
def readB (borrow a : Bool) : Fin 28 :=
  ⟨6 + 2 * borrow.toNat + a.toNat, by cases borrow <;> cases a <;> decide⟩
def backFlag (difference borrow : Bool) : Fin 28 :=
  ⟨10 + 2 * difference.toNat + borrow.toNat, by cases difference <;> cases borrow <;> decide⟩
def writeA (difference borrow : Bool) : Fin 28 :=
  ⟨14 + 2 * difference.toNat + borrow.toNat, by cases difference <;> cases borrow <;> decide⟩
def advance (phase : Fin 4) (borrow : Bool) : Fin 28 :=
  ⟨18 + 2 * phase.val + borrow.toNat, by have hp := phase.isLt; have hb := Bool.toNat_le borrow; omega⟩
def haltLabel (borrow : Bool) : Fin 28 := if borrow then 27 else 26

/-- Twenty-eight labels precede every input and every width. Each iteration
reads A and B, writes only A, and carries one real finite-control borrow. -/
def subMachine : Machine 27 := fun q symbol =>
  if q.val < 2 then some (flagA (decide (q.val = 1)) symbol, .move .right)
  else if q.val < 6 then
    let borrow := decide (4 ≤ q.val)
    let a := decide (q.val % 2 = 1)
    if symbol then some (readB borrow a, .move .right)
    else some (haltLabel borrow, .move .left)
  else if q.val < 10 then
    let borrow := decide (8 ≤ q.val)
    let a := decide (q.val % 2 = 1)
    some (backFlag (differenceBit borrow a symbol) (borrowBit borrow a symbol), .move .left)
  else if q.val < 14 then
    some (writeA (decide (12 ≤ q.val)) (decide (q.val % 2 = 1)), .move .left)
  else if q.val < 18 then
    some (advance 0 (decide (q.val % 2 = 1)), .write (decide (16 ≤ q.val)))
  else if q.val < 26 then
    let borrow := decide (q.val % 2 = 1)
    match (q.val - 18) / 2 with
    | 0 => some (advance 1 borrow, .move .right)
    | 1 => some (advance 2 borrow, .move .right)
    | 2 => some (advance 3 borrow, .move .right)
    | _ => some (readA borrow, .move .right)
  else none

def state (q : Fin 28) (left right : List Bool) : MachineState 27 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem sub_halt (borrow : Bool) (left right : List Bool) :
    Turing.TM0.step subMachine (state (haltLabel borrow) left right) = none := by
  cases borrow <;> simp [Turing.TM0.step, subMachine, state, haltLabel]

theorem subPairs_length (borrow : Bool) (pairs : List (Bool × Bool)) :
    (subPairs borrow pairs).length = pairs.length := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [subPairs, List.length_cons, ih]

theorem subPairs_second (borrow : Bool) (pairs : List (Bool × Bool)) :
    (subPairs borrow pairs).map Prod.snd = pairs.map Prod.snd := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair later ih => obtain ⟨a,b⟩ := pair; simp only [subPairs, List.map_cons, ih]

theorem secondValue_subPairs (borrow : Bool) (pairs : List (Bool × Bool)) :
    secondValue (subPairs borrow pairs) = secondValue pairs := by
  unfold secondValue
  rw [subPairs_second]

theorem firstValue_bound (pairs : List (Bool × Bool)) : firstValue pairs < 2^pairs.length := by
  induction pairs with
  | nil => decide
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit a (firstValue later) < 2^(later.length + 1)
    cases a <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true, Nat.pow_succ] <;> omega

private theorem bit_toNat (bit : Bool) (value : Nat) : Nat.bit bit value = 2 * value + bit.toNat := by
  cases bit <;> rfl

theorem digit_balance (borrow a b : Bool) :
    a.toNat + 2 * (borrowBit borrow a b).toNat =
      (differenceBit borrow a b).toNat + b.toNat + borrow.toNat := by
  cases borrow <;> cases a <;> cases b <;> decide

/-- Exact arithmetic of the same borrow table actually executed by subMachine,
including underflow and empty operands. No value-level repeated subtraction. -/
theorem subtraction_balance (borrow : Bool) (pairs : List (Bool × Bool)) :
    firstValue pairs + 2^pairs.length * (finalBorrow borrow pairs).toNat =
      firstValue (subPairs borrow pairs) + secondValue pairs + borrow.toNat := by
  induction pairs generalizing borrow with
  | nil => cases borrow <;> rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have ht := ih (borrowBit borrow a b)
    have hb := digit_balance borrow a b
    change Nat.bit a (firstValue later) + 2^(later.length + 1) *
      (finalBorrow (borrowBit borrow a b) later).toNat =
      Nat.bit (differenceBit borrow a b) (firstValue (subPairs (borrowBit borrow a b) later)) +
        Nat.bit b (secondValue later) + borrow.toNat
    rw [bit_toNat, bit_toNat, bit_toNat, Nat.pow_succ]
    nlinarith

theorem finalBorrow_eq_false_iff (borrow : Bool) (pairs : List (Bool × Bool)) :
    finalBorrow borrow pairs = false ↔ secondValue pairs + borrow.toNat ≤ firstValue pairs := by
  have balance := subtraction_balance borrow pairs
  have bound := firstValue_bound (subPairs borrow pairs)
  rw [subPairs_length] at bound
  cases hf : finalBorrow borrow pairs
  · simp only [hf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at balance
    constructor
    · intro _; omega
    · intro _; rfl
  · simp only [hf, Bool.toNat_true, Nat.mul_one] at balance
    constructor
    · intro h; cases h
    · intro h; exfalso; omega

theorem subtraction_exact (pairs : List (Bool × Bool)) (hge : secondValue pairs ≤ firstValue pairs) :
    finalBorrow false pairs = false ∧
      firstValue (subPairs false pairs) = firstValue pairs - secondValue pairs := by
  have hf := (finalBorrow_eq_false_iff false pairs).mpr (by simpa only [Bool.toNat_false, Nat.add_zero] using hge)
  have balance := subtraction_balance false pairs
  simp only [hf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at balance
  exact ⟨hf, by omega⟩

theorem subtraction_mod (borrow : Bool) (pairs : List (Bool × Bool)) :
    firstValue (subPairs borrow pairs) =
      (firstValue pairs + 2^pairs.length - (secondValue pairs + borrow.toNat)) % 2^pairs.length := by
  have balance := subtraction_balance borrow pairs
  have bound := firstValue_bound (subPairs borrow pairs)
  rw [subPairs_length] at bound
  cases hf : finalBorrow borrow pairs
  · simp only [hf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at balance
    have heq : firstValue pairs + 2^pairs.length - (secondValue pairs + borrow.toNat) =
        firstValue (subPairs borrow pairs) + 2^pairs.length := by omega
    rw [heq, Nat.add_mod]
    simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt bound]
  · simp only [hf, Bool.toNat_true, Nat.mul_one] at balance
    have heq : firstValue pairs + 2^pairs.length - (secondValue pairs + borrow.toNat) =
        firstValue (subPairs borrow pairs) := by omega
    rw [heq, Nat.mod_eq_of_lt bound]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
