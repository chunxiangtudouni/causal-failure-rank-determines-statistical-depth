module
public import PaperProofs.Common.PSTR_TM_CompactCopy_047

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactUnit048
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompactCode046 PSTRTMCompactCopy047

def paddedDigits (digits : List Bool) : List Bool := digits.flatMap (fun bit => [bit,false])

theorem paddedDigits_length (digits : List Bool) : (paddedDigits digits).length = 2 * digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change (paddedDigits later).length + 2 = 2 * (later.length + 1)
    rw [ih]
    omega

theorem blocks_paddedDigits (digits : List Bool) :
    PSTRTMIncrement009.blocks (paddedDigits digits) = PSTRTMBinaryAdd024.resultColumns digits := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change bit :: true :: false :: true :: PSTRTMIncrement009.blocks (paddedDigits later) =
      bit :: true :: false :: true :: PSTRTMBinaryAdd024.resultColumns later
    rw [ih]

def restoreInitial (a : Bool) (left : List Bool) : List Bool → List Bool → MachineState 54
  | [], right => state 42 (a :: left) (false :: right)
  | bit :: previous, right =>
    state 42 (bit :: (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left)) (true :: right)

def restoreTrace (a : Bool) (left : List Bool) : List Bool → List Bool → List (MachineState 54)
  | [], right => [state 42 (a :: left) (false :: right), state 44 (a :: left) (true :: right)]
  | bit :: previous, right =>
    state 42 (bit :: (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left)) (true :: right) ::
    state 43 (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left) (bit :: true :: right) ::
      restoreTrace a left previous (bit :: true :: right)

theorem restore_head (a : Bool) (left previous right : List Bool) :
    (restoreTrace a left previous right).head? = some (restoreInitial a left previous right) := by
  cases previous <;> rfl

theorem restore_length (a : Bool) (left previous right : List Bool) :
    (restoreTrace a left previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    simp only [restoreTrace, List.length_cons, ih]
    omega

theorem restore_chain (a : Bool) (left previous right : List Bool) :
    (restoreTrace a left previous right).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction previous generalizing right with
  | nil => simp [restoreTrace, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [restoreTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [restore_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> simp [restoreInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem restore_last (a : Bool) (left previous right : List Bool) :
    (restoreTrace a left previous right).getLast? = some
      (state 44 (a :: left) (true :: (PSTRTMIncrement009.blocks previous.reverse ++ right))) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : restoreTrace a left previous (bit :: true :: right) ≠ [] := by
      have hl := restore_length a left previous (bit :: true :: right)
      intro he
      simp [he] at hl
    simp only [restoreTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem copy_restore (a : Bool) (left previous right : List Bool) :
    Turing.TM0.step compactMachine (state 41 (PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left) right) =
      some (restoreInitial a left previous right) := by
  cases previous <;> simp [restoreInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

theorem restore_advance (a : Bool) (left right : List Bool) :
    Turing.TM0.step compactMachine (state 44 (a :: left) (true :: right)) =
      some (state 6 (true :: a :: left) right) := by
  simp [Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

def markTrace (a : Bool) (left right : List Bool) : List (MachineState 54) :=
  [state 6 left (a :: true :: false :: true :: right),
    state 7 (a :: left) (true :: false :: true :: right),
    state 8 (a :: left) (false :: false :: true :: right),
    state 9 (false :: a :: left) (false :: true :: right),
    state 10 (false :: false :: a :: left) (true :: right)]

theorem mark_head (a : Bool) (left right : List Bool) :
    (markTrace a left right).head? = some (state 6 left (a :: true :: false :: true :: right)) := rfl

theorem mark_last (a : Bool) (left right : List Bool) :
    (markTrace a left right).getLast? = some (state 10 (false :: false :: a :: left) (true :: right)) := rfl

theorem mark_length (a : Bool) (left right : List Bool) : (markTrace a left right).length = 5 := rfl

theorem mark_chain (a : Bool) (left right : List Bool) :
    (markTrace a left right).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  simp [markTrace, List.isChain_cons_cons, Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

theorem mark_advance (a : Bool) (left right : List Bool) :
    Turing.TM0.step compactMachine (state 10 (false :: false :: a :: left) (true :: right)) =
      some (state 17 (true :: false :: false :: a :: left) right) := by
  simp [Turing.TM0.step, compactMachine, state, Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 54)) (last first : MachineState 54)
    (hx : xs.IsChain (fun a b => Turing.TM0.step compactMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step compactMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step compactMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step compactMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def unitTrace (a : Bool) (left later : List Bool) : List (MachineState 54) :=
  markTrace a left (PSTRTMBinaryAdd024.resultColumns later ++ [true,false]) ++
    (copyTrace (false :: a :: left) [] (paddedDigits later) false true ++
      restoreTrace a left (paddedDigits later).reverse [true,false])

theorem unit_head (a : Bool) (left later : List Bool) :
    (unitTrace a left later).head? = some
      (state 6 left (PSTRTMBinaryAdd024.resultColumns (a :: later) ++ [true,false])) := by
  simp [unitTrace, List.head?_append, mark_head, PSTRTMBinaryAdd024.resultColumns]

theorem unit_last (a : Bool) (left later : List Bool) :
    (unitTrace a left later).getLast? = some
      (state 44 (a :: left) (true :: (PSTRTMBinaryAdd024.resultColumns later ++ [true,false]))) := by
  simp [unitTrace, List.getLast?_append, restore_last, blocks_paddedDigits]

theorem unit_length (a : Bool) (left later : List Bool) :
    (unitTrace a left later).length = 24 * later.length + 15 := by
  simp only [unitTrace, List.length_append, mark_length, copy_length, restore_length,
    List.length_reverse, paddedDigits_length]
  omega

theorem unit_chain (a : Bool) (left later : List Bool) :
    (unitTrace a left later).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  have hlast : (copyTrace (false :: a :: left) [] (paddedDigits later) false true).getLast? = some
      (state 41 (PSTRTMRawNat010.leftBlocks (paddedDigits later).reverse ++ false :: a :: left) [true,false]) := by
    simpa only [List.append_nil] using copy_last (false :: a :: left) [] (paddedDigits later) false true
  have htail := append_link _ _ _ _ (copy_chain (false :: a :: left) [] (paddedDigits later) false true)
    (restore_chain a left (paddedDigits later).reverse [true,false]) hlast
    (restore_head a left (paddedDigits later).reverse [true,false])
    (copy_restore a left (paddedDigits later).reverse [true,false])
  have hh : (copyTrace (false :: a :: left) [] (paddedDigits later) false true ++
      restoreTrace a left (paddedDigits later).reverse [true,false]).head? = some
        (state 17 (true :: false :: false :: a :: left) (PSTRTMBinaryAdd024.resultColumns later ++ [true,false])) := by
    simp [List.head?_append, copy_head, PSTRTMRawNat010.leftBlocks, blocks_paddedDigits]
  exact append_link _ _ _ _ (mark_chain a left _) htail (mark_last a left _) hh (mark_advance a left _)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactUnit048
