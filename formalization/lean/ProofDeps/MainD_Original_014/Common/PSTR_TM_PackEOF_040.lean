module
public import Common.PSTR_TM_PackLift_037

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackEOF040
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMAlignCode030

def context (a : Bool) (left previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left

/-- Read the second operand's ACTUAL flag, including a real blank EOF.
Only its data bit is held in finite control; no endpoint is supplied. -/
def seekTrace (bit flag a : Bool) (left previous : List Bool) : List Bool → List Bool → List (MachineState 134)
  | [], tail =>
    let old := context a left previous
    [state 3 old (false :: false :: true :: false :: bit :: flag :: tail),
      state 4 (false :: old) (false :: true :: false :: bit :: flag :: tail),
      state 5 (false :: false :: old) (true :: false :: bit :: flag :: tail),
      state 6 (true :: false :: false :: old) (false :: bit :: flag :: tail),
      state 7 (false :: true :: false :: false :: old) (bit :: flag :: tail),
      state (checkB bit) (bit :: false :: true :: false :: false :: old) (flag :: tail)]
  | digit :: later, tail =>
    let old := context a left previous
    state 3 old (digit :: true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: bit :: flag :: tail)) ::
    state 4 (digit :: old) (true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: bit :: flag :: tail)) ::
      seekTrace bit flag a left (digit :: previous) later tail

theorem seek_head (bit flag a : Bool) (left previous digits tail : List Bool) :
    (seekTrace bit flag a left previous digits tail).head? = some
      (state 3 (context a left previous)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail)) := by
  cases digits <;> rfl

theorem seek_last (bit flag a : Bool) (left previous digits tail : List Bool) :
    (seekTrace bit flag a left previous digits tail).getLast? = some
      (state (checkB bit) (bit :: false :: true :: false :: false ::
        context a left (digits.reverse ++ previous)) (flag :: tail)) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons digit later ih =>
    have hne : seekTrace bit flag a left (digit :: previous) later tail ≠ [] := by
      have hh := seek_head bit flag a left (digit :: previous) later tail
      intro h
      simp [h] at hh
    simp only [seekTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem seek_length (bit flag a : Bool) (left previous digits tail : List Bool) :
    (seekTrace bit flag a left previous digits tail).length = 2 * digits.length + 6 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons digit later ih =>
    simp only [seekTrace, List.length_cons, ih]
    omega

set_option maxHeartbeats 800000 in
theorem seek_chain (bit flag a : Bool) (left previous digits tail : List Bool) :
    (seekTrace bit flag a left previous digits tail).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  induction digits generalizing previous with
  | nil => cases bit <;> simp [seekTrace, List.isChain_cons_cons, Turing.TM0.step, alignMachine, state, checkB, Turing.Tape.mk₂]
  | cons digit later ih =>
    rw [seekTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [seek_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂, context, PSTRTMRawNat010.leftBlocks]
    · exact ih _

def markTrace (a bit flag : Bool) (left digits tail : List Bool) : List (MachineState 134) :=
  [state 0 left (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail)),
    state 1 (a :: left) (true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail)),
    state 2 (a :: left) (false :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail))]

theorem mark_chain (a bit flag : Bool) (left digits tail : List Bool) :
    (markTrace a bit flag left digits tail).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  simp [markTrace, List.isChain_cons_cons, Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂]

def scanTrace (a bit flag : Bool) (left digits tail : List Bool) : List (MachineState 134) :=
  markTrace a bit flag left digits tail ++ seekTrace bit flag a left [] digits tail

theorem scan_head (a bit flag : Bool) (left digits tail : List Bool) :
    (scanTrace a bit flag left digits tail).head? = some
      (state 0 left (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail))) := rfl

theorem scan_last (a bit flag : Bool) (left digits tail : List Bool) :
    (scanTrace a bit flag left digits tail).getLast? = some
      (state (checkB bit) (bit :: false :: true :: false :: false :: context a left digits.reverse) (flag :: tail)) := by
  simp [scanTrace, List.getLast?_append, seek_last]

theorem scan_length (a bit flag : Bool) (left digits tail : List Bool) :
    (scanTrace a bit flag left digits tail).length = 2 * digits.length + 9 := by
  simp only [scanTrace, List.length_append, markTrace, List.length_cons, List.length_nil, seek_length]
  omega

theorem scan_chain (a bit flag : Bool) (left digits tail : List Bool) :
    (scanTrace a bit flag left digits tail).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  apply (mark_chain a bit flag left digits tail).append (seek_chain bit flag a left [] digits tail)
  intro before hb after ha
  change some (state 2 (a :: left)
    (false :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: flag :: tail))) = some before at hb
  rw [seek_head] at ha
  have he := Option.some.inj hb
  have hf := Option.mem_some_iff.mp ha
  subst before
  subst after
  simp [Turing.TM0.step, alignMachine, state, context, PSTRTMRawNat010.leftBlocks, Turing.Tape.mk₂]

/-- Two real transitions extend the030 EOF case: write a flagged0 into
blank B, then enter its ordinary finite-phase hole shift at that actual0. -/
theorem eof_write (left : List Bool) :
    Turing.TM0.step PSTRTMPackCode036.packMachine
      (PSTRTMPackCode036.liftAlign (state (checkB false) left [false])) =
      some (PSTRTMPackCode036.state 193 left [true]) := by
  simp [Turing.TM0.step, PSTRTMPackCode036.packMachine, PSTRTMPackCode036.liftAlign,
    PSTRTMPackCode036.embedAlign, PSTRTMPackCode036.state, state, checkB, Turing.Tape.mk₂]

theorem eof_enter (left : List Bool) :
    Turing.TM0.step PSTRTMPackCode036.packMachine
      (PSTRTMPackCode036.state 193 (false :: left) [true]) =
      some (PSTRTMPackCode036.liftAlign (state (hole 2 false) left [false,true])) := by
  simp [Turing.TM0.step, PSTRTMPackCode036.packMachine, PSTRTMPackCode036.liftAlign,
    PSTRTMPackCode036.embedAlign, PSTRTMPackCode036.state, state, hole, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackEOF040
