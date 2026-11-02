module
public import Common.PSTR_TM_AlignCode_030
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignShift031
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMAlignCode030

/-- A real previous two-cell pair is copied right into the hole. Its old
cells become the new hole; every untouched suffix cell keeps its value. -/
def shiftTrace (phase : Fin 3) (bit flag data : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    List (MachineState 134) :=
  [state (hole phase bit) (flag :: data :: left) (x :: y :: right),
    state (previousFlag phase bit) (data :: left) (flag :: x :: y :: right),
    state (readPrevious phase bit flag) left (data :: flag :: x :: y :: right),
    state (moveToHole phase bit flag data) (data :: left) (flag :: x :: y :: right),
    state (writePrevious phase bit flag data) (flag :: data :: left) (x :: y :: right),
    state (moveToFlag phase bit flag) (flag :: data :: left) (data :: y :: right),
    state (writePreviousFlag phase bit flag) (data :: flag :: data :: left) (y :: right),
    state (backFirst (nextPhase phase) bit) (data :: flag :: data :: left) (flag :: right),
    state (backSecond (nextPhase phase) bit) (flag :: data :: left) (data :: flag :: right),
    state (backThird (nextPhase phase) bit) (data :: left) (flag :: data :: flag :: right)]

theorem shift_head (phase : Fin 3) (bit flag data : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (shiftTrace phase bit flag data left x y right).head? = some
      (state (hole phase bit) (flag :: data :: left) (x :: y :: right)) := rfl

theorem shift_length (phase : Fin 3) (bit flag data : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (shiftTrace phase bit flag data left x y right).length = 10 := rfl

theorem shift_last (phase : Fin 3) (bit flag data : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (shiftTrace phase bit flag data left x y right).getLast? = some
      (state (backThird (nextPhase phase) bit) (data :: left) (flag :: data :: flag :: right)) := rfl

private theorem nextPhase_zero : nextPhase (0 : Fin 3) = 0 := by decide

set_option maxHeartbeats 800000 in
private theorem shift_commands (phase : Fin 3) (bit flag data x y : Bool)
    (safe : phase.val ≠ 0 ∨ flag = true) :
    alignMachine (hole phase bit) x = some (previousFlag phase bit, .move .left) ∧
    alignMachine (previousFlag phase bit) flag = some (readPrevious phase bit flag, .move .left) ∧
    alignMachine (readPrevious phase bit flag) data = some (moveToHole phase bit flag data, .move .right) ∧
    alignMachine (moveToHole phase bit flag data) flag = some (writePrevious phase bit flag data, .move .right) ∧
    alignMachine (writePrevious phase bit flag data) x = some (moveToFlag phase bit flag, .write data) ∧
    alignMachine (moveToFlag phase bit flag) data = some (writePreviousFlag phase bit flag, .move .right) ∧
    alignMachine (writePreviousFlag phase bit flag) y = some (backFirst (nextPhase phase) bit, .write flag) ∧
    alignMachine (backFirst (nextPhase phase) bit) flag = some (backSecond (nextPhase phase) bit, .move .left) ∧
    alignMachine (backSecond (nextPhase phase) bit) data = some (backThird (nextPhase phase) bit, .move .left) := by
  fin_cases phase <;> cases flag <;> simp at safe
  all_goals cases bit <;> cases data <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

set_option maxHeartbeats 800000 in
theorem shift_chain (phase : Fin 3) (bit flag data : Bool) (left : List Bool) (x y : Bool) (right : List Bool)
    (safe : phase.val ≠ 0 ∨ flag = true) :
    (shiftTrace phase bit flag data left x y right).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := shift_commands phase bit flag data x y safe
  simp [shiftTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂,
    h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem shift_advance (phase : Fin 3) (bit flag data : Bool) (left right : List Bool) :
    Turing.TM0.step alignMachine
      (state (backThird (nextPhase phase) bit) (data :: left) (flag :: data :: flag :: right)) =
      some (state (hole (nextPhase phase) bit) left (data :: flag :: data :: flag :: right)) := by
  fin_cases phase <;> cases bit <;>
    simp [Turing.TM0.step, alignMachine, state, backThird, hole, nextPhase, Turing.Tape.mk₂]

/-- When the actual marked A flag is encountered, restore it and install
the held actual B digit. No field value or suffix oracle is used. -/
def fillTrace (bit a : Bool) (left : List Bool) (x y : Bool) (right : List Bool) : List (MachineState 134) :=
  [state (hole 0 bit) (false :: a :: left) (x :: y :: right),
    state (previousFlag 0 bit) (a :: left) (false :: x :: y :: right),
    state (restoreAFlag bit) (a :: left) (true :: x :: y :: right),
    state (fillB bit) (true :: a :: left) (x :: y :: right),
    state (moveBFlag bit) (true :: a :: left) (bit :: y :: right),
    state (fillBFlag bit) (bit :: true :: a :: left) (y :: right),
    state (finishColumn bit) (bit :: true :: a :: left) (true :: right),
    state 134 (true :: bit :: true :: a :: left) right]

theorem fill_head (bit a : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (fillTrace bit a left x y right).head? = some
      (state (hole 0 bit) (false :: a :: left) (x :: y :: right)) := rfl

theorem fill_last (bit a : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (fillTrace bit a left x y right).getLast? = some
      (state 134 (true :: bit :: true :: a :: left) right) := rfl

theorem fill_length (bit a : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (fillTrace bit a left x y right).length = 8 := rfl

set_option maxHeartbeats 800000 in
theorem fill_chain (bit a : Bool) (left : List Bool) (x y : Bool) (right : List Bool) :
    (fillTrace bit a left x y right).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  cases bit <;> simp [fillTrace, List.isChain_cons_cons, Turing.TM0.step, alignMachine, state,
    hole, previousFlag, restoreAFlag, fillB, moveBFlag, fillBFlag, finishColumn, Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 134)) (last first : MachineState 134)
    (hx : xs.IsChain (fun a b => Turing.TM0.step alignMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step alignMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step alignMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step alignMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def holeTrace (bit a : Bool) (left : List Bool) : List Bool → Bool → Bool → List Bool → List (MachineState 134)
  | [], x, y, right => fillTrace bit a left x y right
  | digit :: previous, x, y, right =>
    shiftTrace 0 bit true digit (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left) x y right ++
      holeTrace bit a left previous digit true (digit :: true :: right)

theorem hole_head (bit a : Bool) (left previous : List Bool) (x y : Bool) (right : List Bool) :
    (holeTrace bit a left previous x y right).head? = some
      (state (hole 0 bit) (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left) (x :: y :: right)) := by
  cases previous with
  | nil => rfl
  | cons digit previous =>
    simp [holeTrace, List.head?_append, shift_head, PSTRTMRawNat010.leftBlocks]

theorem hole_length (bit a : Bool) (left previous : List Bool) (x y : Bool) (right : List Bool) :
    (holeTrace bit a left previous x y right).length = 10 * previous.length + 8 := by
  induction previous generalizing x y right with
  | nil => rfl
  | cons digit previous ih =>
    simp only [holeTrace, List.length_append, shift_length, ih, List.length_cons]
    omega

theorem hole_last (bit a : Bool) (left previous : List Bool) (x y : Bool) (right : List Bool) :
    (holeTrace bit a left previous x y right).getLast? = some
      (state 134 (true :: bit :: true :: a :: left)
        (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing x y right with
  | nil => rfl
  | cons digit previous ih =>
    simp [holeTrace, List.getLast?_append, ih, PSTRTMIncrement009.blocks,
      List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem hole_chain (bit a : Bool) (left previous : List Bool) (x y : Bool) (right : List Bool) :
    (holeTrace bit a left previous x y right).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  induction previous generalizing x y right with
  | nil => exact fill_chain bit a left x y right
  | cons digit previous ih =>
    rw [holeTrace]
    apply append_link _ _ _ _
      (shift_chain 0 bit true digit _ x y right (Or.inr rfl)) (ih digit true (digit :: true :: right))
      (shift_last 0 bit true digit _ x y right) (hole_head bit a left previous digit true (digit :: true :: right))
    simpa only [nextPhase_zero] using shift_advance 0 bit true digit
      (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left) right

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignShift031
