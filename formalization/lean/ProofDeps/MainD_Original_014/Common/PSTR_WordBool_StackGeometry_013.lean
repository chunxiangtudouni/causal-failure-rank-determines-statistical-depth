module

public import Common.PSTR_WordBool_BoolStackStep_012

/-! Ghost geometry for the ACTUAL lengths in 012. These are proof variables,
not machine-store fields or caller performance qualifications. The bounds
must be inherited from exact initialization; Tape equality alone is weaker. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.StackGeometry

inductive Action where
  | write | halt | right | left

def delta : Action → Int
  | .write | .halt => 0
  | .right => 1
  | .left => -1

def leftSize : Action → Nat → Nat
  | .write, size | .halt, size => size
  | .right, size => size + 1
  | .left, size => size - 1

def rightSize : Action → Nat → Nat
  | .write, size | .halt, size => max size 1
  | .right, size => size - 1
  | .left, size => max size 1 + 1

theorem left_endpoint (action : Action) (position : Int) (left : Nat) :
    position + delta action - (leftSize action left : Int) =
      min (position - (left : Int)) (position + delta action) := by
  cases left <;> cases action <;> dsimp only [delta, leftSize] <;> omega

theorem right_endpoint (action : Action) (position : Int) (right : Nat) :
    position + delta action + (rightSize action right : Int) =
      max (position + (right : Int)) (position + 1) := by
  cases right <;> cases action <;> dsimp only [delta, rightSize] <;> omega

theorem preserves_range (action : Action) (position low high : Int) (left right : Nat)
    (leftBound : low ≤ position - (left : Int))
    (rightBound : position + (right : Int) ≤ high + 1)
    (nextLow : low ≤ position + delta action) (currentHigh : position ≤ high) :
    low ≤ position + delta action - (leftSize action left : Int) ∧
      position + delta action + (rightSize action right : Int) ≤ high + 1 := by
  constructor
  · rw [left_endpoint]
    exact le_min leftBound nextLow
  · rw [right_endpoint]
    exact max_le rightBound (by omega)

theorem mass_of_range (position low high : Int) (left right : Nat)
    (leftBound : low ≤ position - (left : Int))
    (rightBound : position + (right : Int) ≤ high + 1) (nonnegative : 0 ≤ high - low) :
    left + right ≤ (high - low).toNat + 1 := by
  omega

theorem mass_monotone (action : Action) (left right : Nat) :
    left + right ≤ leftSize action left + rightSize action right := by
  have leftEnd := left_endpoint action 0 left
  have rightEnd := right_endpoint action 0 right
  have lower := min_le_left (-(left : Int)) (delta action)
  have upper := le_max_left (right : Int) 1
  omega

theorem left_micro_phases (left right : Nat) :
    let exitMass := (left - 1) + (max right 1 + 1)
    left + right ≤ exitMass ∧ left + (right - 1) ≤ exitMass ∧
      left + max right 1 ≤ exitMass ∧ (left - 1) + max right 1 ≤ exitMass := by
  have retained : right ≤ max right 1 := le_max_left _ _
  dsimp only
  omega

end PaperProofs.Common.Native.PSTRWordBool.StackGeometry
