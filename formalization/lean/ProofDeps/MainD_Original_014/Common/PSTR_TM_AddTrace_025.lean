module
public import Common.PSTR_TM_BinaryAdd_024

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddTrace025
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMBinaryAdd024

def columnTrace (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    List (MachineState 49) :=
  let left := leftResults previous
  let rest := operandColumns later
  let output := sumBit carry a b
  let next := carryBit carry a b
  [state (carryState carry) left (a :: true :: b :: true :: rest),
    state (flagState carry a) (a :: left) (true :: b :: true :: rest),
    state (readBState carry a) (true :: a :: left) (b :: true :: rest),
    state (backState carry a b) (a :: left) (true :: b :: true :: rest),
    state (writeState carry a b) left (a :: true :: b :: true :: rest),
    state (advanceState 0 next) left (output :: true :: b :: true :: rest),
    state (advanceState 1 next) (output :: left) (true :: b :: true :: rest),
    state (advanceState 2 next) (true :: output :: left) (b :: true :: rest),
    state (advanceState 3 next) (true :: output :: left) (false :: true :: rest),
    state (advanceState 4 next) (false :: true :: output :: left) (true :: rest)]

theorem column_head (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    (columnTrace carry a b previous later).head? = some
      (state (carryState carry) (leftResults previous) (operandColumns ((a,b) :: later))) := rfl

theorem column_length (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    (columnTrace carry a b previous later).length = 10 := rfl

theorem column_last (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    (columnTrace carry a b previous later).getLast? = some
      (state (advanceState 4 (carryBit carry a b))
        (false :: true :: sumBit carry a b :: leftResults previous) (true :: operandColumns later)) := rfl

theorem column_chain (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    (columnTrace carry a b previous later).IsChain (fun before after =>
      Turing.TM0.step addMachine before = some after) := by
  cases carry <;> cases a <;> cases b <;>
    simp [columnTrace, List.isChain_cons_cons, Turing.TM0.step, addMachine, state,
      carryState, flagState, readBState, backState, writeState, advanceState,
      sumBit, carryBit, Turing.Tape.mk₂]

theorem column_advance (carry a b : Bool) (previous : List Bool) (later : List (Bool × Bool)) :
    Turing.TM0.step addMachine
      (state (advanceState 4 (carryBit carry a b))
        (false :: true :: sumBit carry a b :: leftResults previous) (true :: operandColumns later)) =
      some (state (carryState (carryBit carry a b)) (leftResults (sumBit carry a b :: previous))
        (operandColumns later)) := by
  cases carry <;> cases a <;> cases b <;>
    simp [Turing.TM0.step, addMachine, state, advanceState, carryState,
      sumBit, carryBit, leftResults, Turing.Tape.mk₂]

def rewindInitial : List Bool → List Bool → MachineState 49
  | [], tail => state 37 [] (false :: tail)
  | bit :: previous, tail => state 37 (false :: true :: bit :: leftResults previous) (true :: tail)

def rewindTrace : List Bool → List Bool → List (MachineState 49)
  | [], tail => [state 37 [] (false :: tail), state 43 [false] tail]
  | bit :: previous, tail =>
    state 37 (false :: true :: bit :: leftResults previous) (true :: tail) ::
    state 38 (true :: bit :: leftResults previous) (false :: true :: tail) ::
    state 39 (bit :: leftResults previous) (true :: false :: true :: tail) ::
    state 40 (leftResults previous) (bit :: true :: false :: true :: tail) ::
      rewindTrace previous (bit :: true :: false :: true :: tail)

theorem rewind_head (previous tail : List Bool) :
    (rewindTrace previous tail).head? = some (rewindInitial previous tail) := by
  cases previous <;> rfl

theorem rewind_length (previous tail : List Bool) :
    (rewindTrace previous tail).length = 4 * previous.length + 2 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    simp only [rewindTrace, List.length_cons, ih]
    omega

theorem rewind_last (previous tail : List Bool) :
    (rewindTrace previous tail).getLast? = some
      (state 43 [false] (resultColumns previous.reverse ++ tail)) := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindTrace previous (bit :: true :: false :: true :: tail) ≠ [] := by
      have hh := rewind_head previous (bit :: true :: false :: true :: tail)
      intro h
      simp [h] at hh
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [resultColumns, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem rewind_chain (previous tail : List Bool) :
    (rewindTrace previous tail).IsChain (fun before after =>
      Turing.TM0.step addMachine before = some after) := by
  induction previous generalizing tail with
  | nil =>
    simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, addMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    simp only [rewindTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, addMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, addMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, addMachine, state, Turing.Tape.mk₂], ?_⟩
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [rewind_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases previous <;> simp [rewindInitial, leftResults, Turing.TM0.step, addMachine, state, Turing.Tape.mk₂]
    · exact ih _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddTrace025
