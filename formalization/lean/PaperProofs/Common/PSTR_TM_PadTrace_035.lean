module
public import PaperProofs.Common.PSTR_TM_PadInsert_034

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPadTrace035
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPadInsert034

private theorem append_link (xs ys : List (MachineState 40)) (last first : MachineState 40)
    (hx : xs.IsChain (fun a b => Turing.TM0.step padMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step padMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step padMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

/-- Copy one actual flagged pair two cells left. The old source cells
become the next hole; the fixed control holds just the source Boolean. -/
def copyUnit (bit x y : Bool) (left right : List Bool) : List (MachineState 40) :=
  [state 17 (y :: x :: left) (bit :: true :: right),
    state (flagMode bit) (bit :: y :: x :: left) (true :: right),
    state (backOne bit) (y :: x :: left) (bit :: true :: right),
    state (backTwo bit) (x :: left) (y :: bit :: true :: right),
    state (writeMode bit) left (x :: y :: bit :: true :: right),
    state (afterWrite bit) left (bit :: y :: bit :: true :: right),
    state 28 (bit :: left) (y :: bit :: true :: right),
    state 29 (bit :: left) (true :: bit :: true :: right),
    state 30 (true :: bit :: left) (bit :: true :: right),
    state 31 (bit :: true :: bit :: left) (true :: right)]

theorem copyUnit_head (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).head? = some
      (state 17 (y :: x :: left) (bit :: true :: right)) := rfl

theorem copyUnit_last (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).getLast? = some
      (state 31 (bit :: true :: bit :: left) (true :: right)) := rfl

theorem copyUnit_length (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).length = 10 := rfl

set_option maxHeartbeats 800000 in
theorem copyUnit_chain (bit x y : Bool) (left right : List Bool) :
    (copyUnit bit x y left right).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  cases bit <;> simp [copyUnit, List.isChain_cons_cons, Turing.TM0.step, padMachine,
    state, flagMode, backOne, backTwo, writeMode, afterWrite, Turing.Tape.mk₂]

theorem copyUnit_advance (bit : Bool) (left right : List Bool) :
    Turing.TM0.step padMachine (state 31 (bit :: true :: bit :: left) (true :: right)) =
      some (state 17 (true :: bit :: true :: bit :: left) right) := by
  simp [Turing.TM0.step, padMachine, state, Turing.Tape.mk₂]

/-- Clear both old source cells, retaining the actual10 marker and tail. -/
def clearTrace (x y : Bool) (left tail : List Bool) : List (MachineState 40) :=
  [state 17 (y :: x :: left) (true :: false :: tail),
    state 19 (true :: y :: x :: left) (false :: tail),
    state 36 (y :: x :: left) (true :: false :: tail),
    state 37 (x :: left) (y :: true :: false :: tail),
    state 38 (x :: left) (false :: true :: false :: tail),
    state 39 left (x :: false :: true :: false :: tail),
    state 40 left (false :: false :: true :: false :: tail)]

theorem clear_head (x y : Bool) (left tail : List Bool) :
    (clearTrace x y left tail).head? = some (state 17 (y :: x :: left) (true :: false :: tail)) := rfl

theorem clear_last (x y : Bool) (left tail : List Bool) :
    (clearTrace x y left tail).getLast? = some (state 40 left (false :: false :: true :: false :: tail)) := rfl

theorem clear_length (x y : Bool) (left tail : List Bool) :
    (clearTrace x y left tail).length = 7 := rfl

theorem clear_chain (x y : Bool) (left tail : List Bool) :
    (clearTrace x y left tail).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  simp [clearTrace, List.isChain_cons_cons, Turing.TM0.step, padMachine, state, Turing.Tape.mk₂]

def copyTrace (previous : List Bool) : List Bool → Bool → Bool → List Bool → List (MachineState 40)
  | [], x, y, tail => clearTrace x y (PSTRTMRawNat010.leftBlocks previous) tail
  | bit :: later, x, y, tail =>
    copyUnit bit x y (PSTRTMRawNat010.leftBlocks previous)
      (PSTRTMIncrement009.blocks later ++ true :: false :: tail) ++
        copyTrace (bit :: previous) later bit true tail

theorem copy_head (previous digits : List Bool) (x y : Bool) (tail : List Bool) :
    (copyTrace previous digits x y tail).head? = some
      (state 17 (y :: x :: PSTRTMRawNat010.leftBlocks previous)
        (PSTRTMIncrement009.blocks digits ++ true :: false :: tail)) := by
  cases digits with
  | nil => rfl
  | cons bit later => simp [copyTrace, List.head?_append, copyUnit_head, PSTRTMIncrement009.blocks]

theorem copy_length (previous digits : List Bool) (x y : Bool) (tail : List Bool) :
    (copyTrace previous digits x y tail).length = 10 * digits.length + 7 := by
  induction digits generalizing previous x y with
  | nil => rfl
  | cons bit later ih =>
    simp only [copyTrace, List.length_append, copyUnit_length, ih, List.length_cons]
    omega

theorem copy_last (previous digits : List Bool) (x y : Bool) (tail : List Bool) :
    (copyTrace previous digits x y tail).getLast? = some
      (state 40 (PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous))
        (false :: false :: true :: false :: tail)) := by
  induction digits generalizing previous x y with
  | nil => rfl
  | cons bit later ih =>
    simp [copyTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem copy_chain (previous digits : List Bool) (x y : Bool) (tail : List Bool) :
    (copyTrace previous digits x y tail).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  induction digits generalizing previous x y with
  | nil => exact clear_chain x y _ tail
  | cons bit later ih =>
    rw [copyTrace]
    apply append_link _ _ _ _
      (copyUnit_chain bit x y _ _) (ih (bit :: previous) bit true)
      (copyUnit_last bit x y _ _) (copy_head (bit :: previous) later bit true tail)
    simpa only [PSTRTMRawNat010.leftBlocks, List.flatMap_cons, List.cons_append,
      List.nil_append] using copyUnit_advance bit (PSTRTMRawNat010.leftBlocks previous)
        (PSTRTMIncrement009.blocks later ++ true :: false :: tail)

/-- Actual rewind uses the already-frozen010 q12/q13 transitions. -/
def rewindInitial : List Bool → List Bool → MachineState 40
  | [], right => state 12 [] (false :: right)
  | bit :: previous, right => state 12 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

def rewindTrace : List Bool → List Bool → List (MachineState 40)
  | [], right => [state 12 [] (false :: right), state 16 [false] right]
  | bit :: previous, right =>
    state 12 (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state 13 (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) ::
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
    (rewindTrace previous right).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  induction previous generalizing right with
  | nil =>
    simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, padMachine, state,
      PSTRTMRawNat010.rawNatMachine, embedRaw, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, padMachine, state, PSTRTMRawNat010.rawNatMachine, embedRaw, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewind_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
        padMachine, state, PSTRTMRawNat010.rawNatMachine, embedRaw, Turing.Tape.mk₂]
    · exact ih _

theorem rewind_last (previous right : List Bool) :
    (rewindTrace previous right).getLast? = some
      (state 16 [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
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

def padTrace (digits tail : List Bool) : List (MachineState 40) :=
  state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail) ::
    (rewindTrace digits.reverse (true :: false :: tail) ++ copyTrace [] digits false false tail)

theorem pad_head (digits tail : List Bool) :
    (padTrace digits tail).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail)) := rfl

theorem pad_length (digits tail : List Bool) :
    (padTrace digits tail).length = 12 * digits.length + 10 := by
  simp only [padTrace, List.length_cons, List.length_append, rewind_length, copy_length, List.length_reverse]
  omega

theorem pad_last (digits tail : List Bool) :
    (padTrace digits tail).getLast? = some
      (state 40 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)) := by
  have hne : rewindTrace digits.reverse (true :: false :: tail) ++ copyTrace [] digits false false tail ≠ [] := by
    intro he
    have hl := congrArg List.length he
    have hc := copy_length [] digits false false tail
    simp only [List.length_append, List.length_nil] at hl
    omega
  rw [padTrace, List.getLast?_cons_of_ne_nil hne]
  simp [List.getLast?_append, copy_last]

theorem pad_chain (digits tail : List Bool) :
    (padTrace digits tail).IsChain (fun a b => Turing.TM0.step padMachine a = some b) := by
  rw [padTrace]
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    simp only [List.head?_append, rewind_head, Option.some_or] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases h : digits.reverse <;> simp [rewindInitial, PSTRTMRawNat010.leftBlocks,
      Turing.TM0.step, padMachine, state, Turing.Tape.mk₂]
  · apply append_link _ _ _ _ (rewind_chain _ _) (copy_chain [] digits false false tail)
      (rewind_last _ _) (copy_head [] digits false false tail)
    rw [List.reverse_reverse]
    have hb : Turing.ListBlank.mk [false,false] = Turing.ListBlank.mk [false] := by
      simpa only [List.cons_append, List.nil_append] using PSTRTMRawNat010.blank_append_false [false]
    change Turing.TM0.step padMachine
      ⟨16, Turing.Tape.mk₂ [false] (PSTRTMIncrement009.blocks digits ++ true :: false :: tail)⟩ =
      some ⟨17, Turing.Tape.mk₂ [false, false] (PSTRTMIncrement009.blocks digits ++ true :: false :: tail)⟩
    rw [show Turing.Tape.mk₂ [false, false] (PSTRTMIncrement009.blocks digits ++ true :: false :: tail) =
      Turing.Tape.mk₂ [false] (PSTRTMIncrement009.blocks digits ++ true :: false :: tail) by
        simp only [Turing.Tape.mk₂]; rw [hb]]
    simp [Turing.TM0.step, padMachine, Turing.Tape.write_self]

/-- The relative prefix is preserved, while TWO actual cells are made
available before the retained marker. The head really moves two cells left. -/
theorem pad_runsFrom (digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom padMachine
      (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse) (true :: false :: tail))
      (padTrace digits tail)
      (state 40 (PSTRTMRawNat010.leftBlocks digits.reverse) (false :: false :: true :: false :: tail)) :=
  ⟨pad_head digits tail, pad_chain digits tail, pad_last digits tail, pad_halt _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPadTrace035
