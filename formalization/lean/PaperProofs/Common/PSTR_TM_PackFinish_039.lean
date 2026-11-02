module
public import PaperProofs.Common.PSTR_TM_PackColumns_038

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFinish039
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

def rewindInitial : List Bool → List Bool → MachineState 193
  | [], right => state 190 [] (false :: right)
  | bit :: previous, right => state 190 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

def rewindTrace : List Bool → List Bool → List (MachineState 193)
  | [], right => [state 190 [] (false :: right), state 192 [false] right]
  | bit :: previous, right =>
    state 190 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state 191 (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) ::
      rewindTrace previous (bit :: true :: right)

theorem rewind_head (previous right : List Bool) :
    (rewindTrace previous right).head? = some (rewindInitial previous right) := by
  cases previous <;> rfl

theorem rewind_length (previous right : List Bool) :
    (rewindTrace previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    simp only [rewindTrace, List.length_cons, ih]
    omega

theorem rewind_chain (previous right : List Bool) :
    (rewindTrace previous right).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  induction previous generalizing right with
  | nil => simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewind_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks,
        Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem rewind_last (previous right : List Bool) :
    (rewindTrace previous right).getLast? = some
      (state 192 [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindTrace previous (bit :: true :: right) ≠ [] := by
      have hlen := rewind_length previous (bit :: true :: right)
      intro h
      simp [h] at hlen
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- The actual isolated EOF cells read by q5/q6 are blank. The retained
separator's sole true cell is erased before rewinding the produced columns. -/
def clearTrace (previous : List Bool) : List (MachineState 193) :=
  let left := PSTRTMRawNat010.leftBlocks previous
  [state 0 left [false,false,true,false],
    state 1 (false :: left) [false,true,false],
    state 3 (false :: false :: left) [true,false],
    state 4 (true :: false :: false :: left) [false],
    state 5 (false :: true :: false :: false :: left) [],
    state 6 (false :: false :: true :: false :: false :: left) [],
    state 8 (false :: true :: false :: false :: left) [false],
    state 9 (true :: false :: false :: left) [false,false],
    state 186 (false :: false :: left) [true,false,false],
    state 187 (false :: false :: left) [false,false,false],
    state 188 (false :: left) [false,false,false,false],
    state 189 left [false,false,false,false,false]]

theorem clear_head (previous : List Bool) :
    (clearTrace previous).head? = some (state 0 (PSTRTMRawNat010.leftBlocks previous) [false,false,true,false]) := rfl

theorem clear_last (previous : List Bool) :
    (clearTrace previous).getLast? = some
      (state 189 (PSTRTMRawNat010.leftBlocks previous) [false,false,false,false,false]) := rfl

theorem clear_length (previous : List Bool) : (clearTrace previous).length = 12 := rfl

set_option maxHeartbeats 800000 in
theorem clear_chain (previous : List Bool) :
    (clearTrace previous).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  simp [clearTrace, List.isChain_cons_cons, Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]

theorem clear_advance (previous : List Bool) :
    Turing.TM0.step packMachine
      (state 189 (PSTRTMRawNat010.leftBlocks previous) [false,false,false,false,false]) =
      some (rewindInitial previous [false,false,false,false,false]) := by
  cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks,
    Turing.TM0.step, packMachine, state, Turing.Tape.mk₂]

def finishTrace (previous : List Bool) : List (MachineState 193) :=
  clearTrace previous ++ rewindTrace previous [false,false,false,false,false]

theorem finish_head (previous : List Bool) :
    (finishTrace previous).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous) [false,false,true,false]) := by
  simp [finishTrace, List.head?_append, clear_head]

theorem finish_last (previous : List Bool) :
    (finishTrace previous).getLast? = some
      (state 192 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false,false,false,false])) := by
  simp [finishTrace, List.getLast?_append, rewind_last]

theorem finish_length (previous : List Bool) :
    (finishTrace previous).length = 2 * previous.length + 14 := by
  simp only [finishTrace, List.length_append, clear_length, rewind_length]
  omega

theorem finish_chain (previous : List Bool) :
    (finishTrace previous).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  apply (clear_chain previous).append (rewind_chain previous _)
  intro before hb after ha
  simp only [clear_last, Option.mem_some_iff] at hb
  simp only [rewind_head, Option.mem_some_iff] at ha
  subst before
  subst after
  exact clear_advance previous

theorem blank_false_suffix (bits : List Bool) (n : Nat) :
    Turing.ListBlank.mk (bits ++ List.replicate n false) = Turing.ListBlank.mk bits := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, PSTRTMRawNat010.blank_append_false, ih]

theorem finish_final_tape (previous : List Bool) :
    (state 192 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false,false,false,false])).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks previous.reverse) := by
  have hr : Turing.ListBlank.mk
      (PSTRTMIncrement009.blocks previous.reverse ++ [false,false,false,false,false]) =
      Turing.ListBlank.mk (PSTRTMIncrement009.blocks previous.reverse) := by
    simpa only [List.replicate_succ, List.replicate_zero] using
      blank_false_suffix (PSTRTMIncrement009.blocks previous.reverse) 5
  simp only [state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false, hr]

theorem finish_runsFrom (previous : List Bool) :
    PSTRTMSeq005.RunsFrom packMachine
      (state 0 (PSTRTMRawNat010.leftBlocks previous) [false,false,true,false])
      (finishTrace previous)
      (state 192 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false,false,false,false])) :=
  ⟨finish_head previous, finish_chain previous, finish_last previous, pack_halt _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFinish039
