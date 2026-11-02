module
public import Common.PSTR_TM_CompactUnit_048

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactFinish049
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompactCode046

def rewindInitial : List Bool → List Bool → MachineState 54
  | [], right => state 52 [] (false :: right)
  | bit :: previous, right => state 52 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

def rewindTrace : List Bool → List Bool → List (MachineState 54)
  | [], right => [state 52 [] (false :: right), state 54 [false] right]
  | bit :: previous, right =>
    state 52 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state 53 (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) :: rewindTrace previous (bit :: true :: right)

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
    (rewindTrace previous right).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction previous generalizing right with
  | nil => simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewind_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem rewind_last (previous right : List Bool) :
    (rewindTrace previous right).getLast? = some
      (state 54 [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindTrace previous (bit :: true :: right) ≠ [] := by
      have hl := rewind_length previous (bit :: true :: right)
      intro he
      simp [he] at hl
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- Only the real endmarker's1 is cleared. Every earlier compacted pair
remains on tape and is traversed by the actual final flag rewind. -/
def finishPrefix (previous : List Bool) : List (MachineState 54) :=
  let left := PSTRTMRawNat010.leftBlocks previous
  [state 6 left [true,false], state 7 (true :: left) [false],
    state 50 left [true,false], state 51 left [false,false]]

theorem prefix_head (previous : List Bool) :
    (finishPrefix previous).head? = some (state 6 (PSTRTMRawNat010.leftBlocks previous) [true,false]) := rfl

theorem prefix_last (previous : List Bool) :
    (finishPrefix previous).getLast? = some (state 51 (PSTRTMRawNat010.leftBlocks previous) [false,false]) := rfl

theorem prefix_length (previous : List Bool) : (finishPrefix previous).length = 4 := rfl

theorem prefix_chain (previous : List Bool) :
    (finishPrefix previous).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  simp [finishPrefix, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

theorem prefix_advance (previous : List Bool) :
    Turing.TM0.step compactMachine (state 51 (PSTRTMRawNat010.leftBlocks previous) [false,false]) =
      some (rewindInitial previous [false,false]) := by
  cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

def finishTrace (previous : List Bool) : List (MachineState 54) :=
  finishPrefix previous ++ rewindTrace previous [false,false]

theorem finish_head (previous : List Bool) :
    (finishTrace previous).head? = some (state 6 (PSTRTMRawNat010.leftBlocks previous) [true,false]) := by
  simp only [finishTrace, List.head?_append, prefix_head, Option.some_or]

theorem finish_last (previous : List Bool) :
    (finishTrace previous).getLast? = some
      (state 54 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false])) := by
  simp only [finishTrace, List.getLast?_append, rewind_last, Option.some_or]

theorem finish_length (previous : List Bool) : (finishTrace previous).length = 2 * previous.length + 6 := by
  simp only [finishTrace, List.length_append, prefix_length, rewind_length]
  omega

theorem finish_chain (previous : List Bool) :
    (finishTrace previous).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  apply (prefix_chain previous).append (rewind_chain previous _)
  intro before hb after ha
  simp only [prefix_last, Option.mem_some_iff] at hb
  simp only [rewind_head, Option.mem_some_iff] at ha
  subst before
  subst after
  exact prefix_advance previous

theorem finish_final_tape (previous : List Bool) :
    (state 54 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false])).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks previous.reverse) := by
  have hr : Turing.ListBlank.mk (PSTRTMIncrement009.blocks previous.reverse ++ [false,false]) =
      Turing.ListBlank.mk (PSTRTMIncrement009.blocks previous.reverse) := by
    simpa only [List.replicate_succ, List.replicate_zero] using
      PSTRTMPackFinish039.blank_false_suffix (PSTRTMIncrement009.blocks previous.reverse) 2
  simp only [state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false, hr]

theorem finish_runsFrom (previous : List Bool) :
    PSTRTMSeq005.RunsFrom compactMachine
      (state 6 (PSTRTMRawNat010.leftBlocks previous) [true,false]) (finishTrace previous)
      (state 54 [false] (PSTRTMIncrement009.blocks previous.reverse ++ [false,false])) :=
  ⟨finish_head previous, finish_chain previous, finish_last previous, compact_halt _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactFinish049
