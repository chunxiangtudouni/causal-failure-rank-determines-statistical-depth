module
public import Common.PSTR_TM_RawPack_045

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

/-- Actual backward erasure of flagged bits. A real false left guard stops
the scan. Neither an endpoint nor the number of bits is supplied to code. -/
def eraseMachine : Machine 5 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => if symbol then some (2, .write false) else some (5, .move .right)
  | 2 => some (3, .move .left)
  | 3 => some (4, .write false)
  | 4 => some (1, .move .left)
  | _ => none

def eraseState (q : Fin 6) (left right : List Bool) : MachineState 5 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def eraseInitial (archive : List Bool) : List Bool → Nat → List Bool → MachineState 5
  | [], cleared, tail => eraseState 1 archive (false :: (List.replicate cleared false ++ tail))
  | bit :: previous, cleared, tail =>
      eraseState 1 (bit :: (PSTRTMRawNat010.leftBlocks previous ++ false :: archive))
        (true :: (List.replicate cleared false ++ tail))

def eraseUnit (archive : List Bool) (bit : Bool) (previous : List Bool)
    (cleared : Nat) (tail : List Bool) : List (MachineState 5) :=
  let left := PSTRTMRawNat010.leftBlocks previous ++ false :: archive
  let right := List.replicate cleared false ++ tail
  [eraseState 1 (bit :: left) (true :: right),
   eraseState 2 (bit :: left) (false :: right),
   eraseState 3 left (bit :: false :: right),
   eraseState 4 left (false :: false :: right)]

theorem eraseUnit_head (archive : List Bool) (bit : Bool) (previous : List Bool)
    (cleared : Nat) (tail : List Bool) :
    (eraseUnit archive bit previous cleared tail).head? =
      some (eraseInitial archive (bit :: previous) cleared tail) := rfl

theorem eraseUnit_last (archive : List Bool) (bit : Bool) (previous : List Bool)
    (cleared : Nat) (tail : List Bool) :
    (eraseUnit archive bit previous cleared tail).getLast? =
      some (eraseState 4 (PSTRTMRawNat010.leftBlocks previous ++ false :: archive)
        (false :: false :: (List.replicate cleared false ++ tail))) := rfl

theorem eraseUnit_chain (archive : List Bool) (bit : Bool) (previous : List Bool)
    (cleared : Nat) (tail : List Bool) :
    (eraseUnit archive bit previous cleared tail).IsChain
      (fun before after => Turing.TM0.step eraseMachine before = some after) := by
  simp [eraseUnit, List.isChain_cons_cons, Turing.TM0.step, eraseMachine,
    eraseState, Turing.Tape.mk₂]

theorem eraseUnit_advance (archive previous : List Bool) (cleared : Nat) (tail : List Bool) :
    Turing.TM0.step eraseMachine
      (eraseState 4 (PSTRTMRawNat010.leftBlocks previous ++ false :: archive)
        (false :: false :: (List.replicate cleared false ++ tail))) =
      some (eraseInitial archive previous (cleared + 2) tail) := by
  cases previous <;> simp [eraseInitial, PSTRTMRawNat010.leftBlocks,
    Turing.TM0.step, eraseMachine, eraseState, Turing.Tape.mk₂, List.replicate_succ]

def eraseTrace (archive : List Bool) : List Bool → Nat → List Bool → List (MachineState 5)
  | [], cleared, tail =>
      [eraseInitial archive [] cleared tail,
       eraseState 5 (false :: archive) (List.replicate cleared false ++ tail)]
  | bit :: previous, cleared, tail =>
      eraseUnit archive bit previous cleared tail ++ eraseTrace archive previous (cleared + 2) tail

theorem eraseTrace_head (archive previous : List Bool) (cleared : Nat) (tail : List Bool) :
    (eraseTrace archive previous cleared tail).head? =
      some (eraseInitial archive previous cleared tail) := by
  cases previous <;> simp [eraseTrace, List.head?_append, eraseUnit_head]

theorem eraseTrace_last (archive previous : List Bool) (cleared : Nat) (tail : List Bool) :
    (eraseTrace archive previous cleared tail).getLast? =
      some (eraseState 5 (false :: archive)
        (List.replicate (cleared + 2 * previous.length) false ++ tail)) := by
  induction previous generalizing cleared with
  | nil => simp [eraseTrace]
  | cons bit previous ih =>
      simp only [eraseTrace, List.getLast?_append, ih, Option.some_or, List.length_cons]
      congr 4
      omega

theorem eraseTrace_length (archive previous : List Bool) (cleared : Nat) (tail : List Bool) :
    (eraseTrace archive previous cleared tail).length = 4 * previous.length + 2 := by
  induction previous generalizing cleared with
  | nil => rfl
  | cons bit previous ih =>
      simp only [eraseTrace, List.length_append, eraseUnit, List.length_cons, List.length_nil, ih]
      omega

theorem eraseTrace_chain (archive previous : List Bool) (cleared : Nat) (tail : List Bool) :
    (eraseTrace archive previous cleared tail).IsChain
      (fun before after => Turing.TM0.step eraseMachine before = some after) := by
  induction previous generalizing cleared with
  | nil =>
      simp [eraseTrace, eraseInitial, List.isChain_cons_cons, Turing.TM0.step,
        eraseMachine, eraseState, Turing.Tape.mk₂]
  | cons bit previous ih =>
      apply (eraseUnit_chain archive bit previous cleared tail).append (ih (cleared + 2))
      intro before hb after ha
      rw [eraseUnit_last] at hb
      rw [eraseTrace_head] at ha
      have he := Option.mem_some_iff.mp hb
      have hf := Option.mem_some_iff.mp ha
      subst before
      subst after
      exact eraseUnit_advance archive previous cleared tail

def eraseFullTrace (archive digits tail : List Bool) : List (MachineState 5) :=
  eraseState 0 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: archive) tail ::
    eraseTrace archive digits.reverse 0 tail

/-- Whole-tape cleanup contract: every data and flag cell is actually
written false. The archive beyond the real guard and the arbitrary tail
are retained exactly; the head returns to the first erased data cell. -/
theorem erase_runsFrom (archive digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom eraseMachine
      (eraseState 0 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: archive) tail)
      (eraseFullTrace archive digits tail)
      (eraseState 5 (false :: archive) (List.replicate (2 * digits.length) false ++ tail)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [eraseTrace_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases digits.reverse <;>
        simp [eraseInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
          eraseMachine, eraseState, Turing.Tape.mk₂]
    · exact eraseTrace_chain archive digits.reverse 0 tail
  · have hn : eraseTrace archive digits.reverse 0 tail ≠ [] := by
      intro h
      have hh := eraseTrace_head archive digits.reverse 0 tail
      simp [h] at hh
    simp only [eraseFullTrace, List.getLast?_cons_of_ne_nil hn, eraseTrace_last,
      List.length_reverse, Nat.zero_add]
  · simp [Turing.TM0.step, eraseMachine, eraseState]

theorem eraseFullTrace_length (archive digits tail : List Bool) :
    (eraseFullTrace archive digits tail).length = 4 * digits.length + 3 := by
  simp only [eraseFullTrace, List.length_cons, eraseTrace_length, List.length_reverse]

theorem eraseFullTrace_visitedSpace_le (inputLength : Nat) (archive digits tail : List Bool) :
    visitedSpace eraseMachine inputLength (eraseFullTrace archive digits tail) ≤
      inputLength + 8 * digits.length + 7 := by
  have hs := PSTRTMTrace002.visitedSpace_le eraseMachine inputLength (eraseFullTrace archive digits tail)
  rw [eraseFullTrace_length] at hs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
