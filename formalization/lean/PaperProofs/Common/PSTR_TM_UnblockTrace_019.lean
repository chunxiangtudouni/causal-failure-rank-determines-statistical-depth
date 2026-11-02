module
public import PaperProofs.Common.PSTR_TM_Unblock_018

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMUnblockTrace019
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMUnblock018 PSTRTMTrace002

private theorem append_link (xs ys : List (MachineState 19)) (last first : MachineState 19)
    (hx : xs.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step unblockMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def rawWord (digits : List Bool) : List Bool :=
  List.replicate digits.length true ++ false :: digits

def doneTrace (tail : List Bool) : List (MachineState 19) :=
  [state 2 [] (rawWord tail), state 3 [] (false :: rawWord tail), state 19 [false] (rawWord tail)]

theorem done_chain (tail : List Bool) :
    (doneTrace tail).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  simp [doneTrace, List.isChain_cons_cons, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂]

def undoTrace : List Bool → List Bool → List (MachineState 19)
  | [], tail => doneTrace tail
  | bit :: previous, tail => inverseUnit bit previous tail ++ undoTrace previous (bit :: tail)

theorem undo_head (previous tail : List Bool) :
    (undoTrace previous tail).head? = some
      (state 2 (PSTRTMRawNat010.leftBlocks previous) (rawWord tail)) := by
  cases previous with
  | nil => rfl
  | cons bit previous => simp [undoTrace, List.head?_append, inverseUnit_head, rawWord]

theorem undo_length (previous tail : List Bool) :
    (undoTrace previous tail).length = previous.length ^ 2 + 2 * tail.length * previous.length +
      9 * previous.length + 3 := by
  induction previous generalizing tail with
  | nil => rfl
  | cons bit previous ih =>
    simp only [undoTrace, List.length_append, inverseUnit_length, ih, List.length_cons]
    ring

theorem undo_last (previous tail : List Bool) :
    (undoTrace previous tail).getLast? = some
      (state 19 [false]
        (List.replicate (previous.length + tail.length) true ++ false :: (previous.reverse ++ tail))) := by
  induction previous generalizing tail with
  | nil => simp [undoTrace, doneTrace, rawWord]
  | cons bit previous ih =>
    simp [undoTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc,
      Nat.add_left_comm, Nat.add_comm]

theorem undo_chain (previous tail : List Bool) :
    (undoTrace previous tail).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  induction previous generalizing tail with
  | nil => exact done_chain tail
  | cons bit previous ih =>
    rw [undoTrace]
    apply append_link _ _ _ _ (inverseUnit_chain bit previous tail) (ih (bit :: tail))
      (inverseUnit_last bit previous tail) (undo_head previous (bit :: tail))
    simp [Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂, rawWord, List.replicate_succ]

/-- The first actual pass locates the end by reading the flag cell of every
input block. The two final blank configurations refer to genuine blank tape. -/
def seekTrace (previous : List Bool) : List Bool → List (MachineState 19)
  | [] => [state 0 (PSTRTMRawNat010.leftBlocks previous) [],
      state 1 (false :: PSTRTMRawNat010.leftBlocks previous) []]
  | bit :: later =>
    state 0 (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks (bit :: later)) ::
    state 1 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: PSTRTMIncrement009.blocks later) ::
      seekTrace (bit :: previous) later

theorem seek_head (previous digits : List Bool) :
    (seekTrace previous digits).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks digits)) := by
  cases digits <;> rfl

theorem seek_length (previous digits : List Bool) :
    (seekTrace previous digits).length = 2 * digits.length + 2 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    simp only [seekTrace, List.length_cons, ih]
    omega

theorem seek_last (previous digits : List Bool) :
    (seekTrace previous digits).getLast? = some
      (state 1 (false :: PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous)) []) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hne : seekTrace (bit :: previous) later ≠ [] := by
      have hh := seek_head (bit :: previous) later
      intro h
      simp [h] at hh
    simp only [seekTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem seek_chain (previous digits : List Bool) :
    (seekTrace previous digits).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  induction digits generalizing previous with
  | nil =>
    simp [seekTrace, List.isChain_cons_cons, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [seekTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂, PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [seek_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂, PSTRTMRawNat010.leftBlocks]
    · exact ih _

def unblockTrace (digits : List Bool) : List (MachineState 19) :=
  seekTrace [] digits ++ undoTrace digits.reverse []

theorem unblock_length (digits : List Bool) :
    (unblockTrace digits).length = digits.length ^ 2 + 11 * digits.length + 5 := by
  simp only [unblockTrace, List.length_append, seek_length, undo_length,
    List.length_reverse, List.length_nil]
  ring

theorem unblock_chain (digits : List Bool) :
    (unblockTrace digits).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  apply append_link _ _ _ _ (seek_chain [] digits) (undo_chain digits.reverse [])
    (seek_last [] digits) (undo_head digits.reverse [])
  simp [Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂, rawWord,
    PSTRTMRawNat010.blank_single_false]

theorem unblock_halt (left right : List Bool) :
    Turing.TM0.step unblockMachine (state 19 left right) = none := by
  simp [Turing.TM0.step, unblockMachine, state]

theorem unblock_runs (digits : List Bool) :
    Runs unblockMachine (PSTRTMIncrement009.blocks digits) (unblockTrace digits)
      (state 19 [false] (rawWord digits)) := by
  apply runs_of_chain
  · simp [unblockTrace, List.head?_append, seek_head, Turing.TM0.init,
      state, Turing.Tape.mk₁, PSTRTMRawNat010.leftBlocks]
  · exact unblock_chain digits
  · simp [unblockTrace, List.getLast?_append, undo_last, rawWord]
  · exact unblock_halt _ _

/-- A genuine inverse Bool codec with actual quadratic time and original
visitedSpace. This call expects isolated blocks; no arbitrary-suffix frame
law is assumed. Whole-tape equality supplies the later sequence contract. -/
theorem unblock_computes (digits : List Bool) :
    computes unblockMachine (PSTRTMIncrement009.blocks digits) (rawWord digits)
      (128 * (digits.length + 1)^2) (128 * (digits.length + 1)^2) := by
  refine ⟨unblockTrace digits, state 19 [false] (rawWord digits), unblock_runs digits, ?_, ?_, ?_⟩
  · simp [state, Turing.Tape.mk₂]
  · rw [unblock_length]
    nlinarith
  · have hs := visitedSpace_le unblockMachine (PSTRTMIncrement009.blocks digits).length (unblockTrace digits)
    rw [PSTRTMIncrement009.blocks_length, unblock_length] at hs
    rw [PSTRTMIncrement009.blocks_length]
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMUnblockTrace019
