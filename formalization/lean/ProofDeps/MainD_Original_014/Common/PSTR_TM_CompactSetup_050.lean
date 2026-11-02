module
public import Common.PSTR_TM_CompactFinish_049

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactSetup050
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompactCode046

/-- Scan every real pair flag, then allocate the endmarker's1 on actual
blank EOF. The following real blank was just read by q1; no marker input. -/
def scanTrace (previous : List Bool) : List Bool → List (MachineState 54)
  | [] =>
    let left := PSTRTMRawNat010.leftBlocks previous
    [state 0 left [], state 1 (false :: left) [], state 2 left [false], state 3 left [true]]
  | bit :: later =>
    state 0 (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: PSTRTMIncrement009.blocks later) ::
    state 1 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: PSTRTMIncrement009.blocks later) ::
      scanTrace (bit :: previous) later

theorem scan_head (previous digits : List Bool) :
    (scanTrace previous digits).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks digits)) := by
  cases digits <;> rfl

theorem scan_length (previous digits : List Bool) :
    (scanTrace previous digits).length = 2 * digits.length + 4 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    simp only [scanTrace, List.length_cons, ih]
    omega

theorem scan_chain (previous digits : List Bool) :
    (scanTrace previous digits).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction digits generalizing previous with
  | nil => simp [scanTrace, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [scanTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [scan_head, Option.mem_some_iff] at ha
      subst after
      simp [PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem scan_last (previous digits : List Bool) :
    (scanTrace previous digits).getLast? = some
      (state 3 (PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous)) [true]) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hne : scanTrace (bit :: previous) later ≠ [] := by
      have hl := scan_length (bit :: previous) later
      intro he
      simp [he] at hl
    simp only [scanTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [List.reverse_cons, List.append_assoc]

def rewindInitial : List Bool → List Bool → MachineState 54
  | [], right => state 4 [] (false :: right)
  | bit :: previous, right => state 4 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

/-- End BEFORE q4's actual final right transfer to the q6 compaction loop. -/
def rewindTrace : List Bool → List Bool → List (MachineState 54)
  | [], right => [state 4 [] (false :: right)]
  | bit :: previous, right =>
    state 4 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state 5 (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) :: rewindTrace previous (bit :: true :: right)

theorem rewind_head (previous right : List Bool) :
    (rewindTrace previous right).head? = some (rewindInitial previous right) := by
  cases previous <;> rfl

theorem rewind_length (previous right : List Bool) :
    (rewindTrace previous right).length = 2 * previous.length + 1 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    simp only [rewindTrace, List.length_cons, ih]
    omega

theorem rewind_chain (previous right : List Bool) :
    (rewindTrace previous right).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction previous generalizing right with
  | nil => exact .singleton _
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
      (state 4 [] (false :: (PSTRTMIncrement009.blocks previous.reverse ++ right))) := by
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

theorem scan_advance (previous right : List Bool) :
    Turing.TM0.step compactMachine (state 3 (PSTRTMRawNat010.leftBlocks previous) right) =
      some (rewindInitial previous right) := by
  cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

def setupTrace (digits : List Bool) : List (MachineState 54) :=
  scanTrace [] digits ++ rewindTrace digits.reverse [true]

theorem setup_head (digits : List Bool) :
    (setupTrace digits).head? = some (state 0 [] (PSTRTMIncrement009.blocks digits)) := by
  simp [setupTrace, List.head?_append, scan_head, PSTRTMRawNat010.leftBlocks]

theorem setup_last (digits : List Bool) :
    (setupTrace digits).getLast? = some (state 4 [] (false :: (PSTRTMIncrement009.blocks digits ++ [true]))) := by
  simp [setupTrace, List.getLast?_append, rewind_last]

theorem setup_length (digits : List Bool) : (setupTrace digits).length = 4 * digits.length + 5 := by
  simp only [setupTrace, List.length_append, scan_length, rewind_length, List.length_reverse]
  omega

theorem setup_chain (digits : List Bool) :
    (setupTrace digits).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  apply (scan_chain [] digits).append (rewind_chain digits.reverse [true])
  intro before hb after ha
  simp only [scan_last, List.append_nil, Option.mem_some_iff] at hb
  simp only [rewind_head, Option.mem_some_iff] at ha
  subst before
  subst after
  exact scan_advance digits.reverse [true]

/-- The actual final q4 right move establishes the whole q6 entry tape.
The marker flag0 is the real blank read earlier at EOF, not supplied data. -/
theorem setup_advance (digits : List Bool) :
    Turing.TM0.step compactMachine (state 4 [] (false :: (PSTRTMIncrement009.blocks digits ++ [true]))) =
      some (state 6 [] (PSTRTMIncrement009.blocks digits ++ [true,false])) := by
  let word := PSTRTMIncrement009.blocks digits ++ [true]
  have hr : Turing.ListBlank.mk (PSTRTMIncrement009.blocks digits ++ [true,false]) = Turing.ListBlank.mk word := by
    simpa only [word, List.append_assoc, List.singleton_append] using PSTRTMRawNat010.blank_append_false word
  have he : state 6 [] (PSTRTMIncrement009.blocks digits ++ [true,false]) = state 6 [false] word := by
    simp only [state, Turing.Tape.mk₂]
    rw [hr, PSTRTMRawNat010.blank_single_false]
  rw [he]
  simp [word, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactSetup050
