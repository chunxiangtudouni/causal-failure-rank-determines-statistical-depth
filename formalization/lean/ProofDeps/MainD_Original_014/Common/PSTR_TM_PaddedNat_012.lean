module
public import Common.PSTR_TM_RawNat_010

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPaddedNat012
open PaperProofs.Common.Native.RationalControllerComputation

/-- Preserve the raw decoder's seventeen finite labels. -/
def embedRaw (q : Fin 17) : Fin 107 := ⟨q.val, by omega⟩

/-- A saved PUBLIC suffix bit is held in finite control during footer work.
Each block has45 fixed phases, independent of every numeric input. -/
def post (saved : Bool) (phase : Fin 45) : Fin 107 :=
  ⟨17 + (if saved then 45 else 0) + phase.val, by
    have h := phase.isLt
    cases saved <;> dsimp <;> omega⟩

/-- Full fixed code for the next raw-field transport. Internal end10 is
kept AFTER real00 padding. Copying shifts only the operand three cells left;
all original suffix cells are restored at their original physical addresses.
No performance theorem for this new program is claimed until its full trace
is checked. Prefix rotations reuse the frozen raw machine. -/
def paddedNatMachine : Machine 106 := fun q symbol =>
  if h : q.val < 17 then
    if q.val = 0 ∧ symbol = false then some (post false 0, .move .right)
    else (PSTRTMRawNat010.rawNatMachine ⟨q.val, h⟩ symbol).map
      (fun (next, statement) => (embedRaw next, statement))
  else
    let index := q.val - 17
    let saved := decide (45 ≤ index)
    match index % 45 with
    | 0 => some (post symbol 1, .write false)
    | 1 => some (post saved 2, .move .left)
    | 2 => some (post saved 3, .write true)
    | 3 => some (post saved 4, .move .left)
    | 4 => some (post saved (if symbol then 5 else 6), if symbol then .move .left else .move .right)
    | 5 => some (post saved 4, .move .left)
    | 6 => some (post saved (if symbol then 8 else 7), .move .right)
    | 7 => if symbol then some (post saved 9, .move .left) else none
    | 8 => some (post saved (if symbol then 17 else 25), .move .left)
    | 9 => some (post saved 10, .move .left)
    | 10 => some (post saved 11, .move .left)
    | 11 => some (post saved 12, .move .left)
    | 12 => some (post saved 13, .write false)
    | 13 => some (post saved 14, .move .right)
    | 14 => some (post saved 15, .write true)
    | 15 => some (post saved 16, .move .right)
    | 16 => some (post saved 21, .move .right)
    | 17 => some (post saved 18, .move .left)
    | 18 => some (post saved 19, .move .left)
    | 19 => some (post saved 20, .move .left)
    | 20 => some (post saved 13, .write true)
    | 21 => some (post saved 22, .move .right)
    | 22 => some (post saved 6, .move .right)
    | 25 => some (post saved 26, .move .left)
    | 26 => some (post saved 27, .move .left)
    | 27 => some (post saved 28, .move .left)
    | 28 => some (post saved 29, .write false)
    | 29 => some (post saved 30, .move .right)
    | 30 => some (post saved 31, .write false)
    | 31 => some (post saved 32, .move .right)
    | 32 => some (post saved 33, .write true)
    | 33 => some (post saved 34, .move .right)
    | 34 => some (post saved 35, .write false)
    | 35 => some (post saved 36, .move .right)
    | 36 => some (post saved 37, .write saved)
    | 37 => some (post saved 38, .move .left)
    | 38 => some (post saved 39, .move .left)
    | 39 => some (post saved 40, .move .left)
    | 40 => some (post saved 41, .move .left)
    | 41 => some (post saved 42, .move .left)
    | 42 => some (post saved (if symbol then 43 else 44), if symbol then .move .left else .move .right)
    | 43 => some (post saved 42, .move .left)
    | _ => none

def state (q : Fin 107) (left right : List Bool) : MachineState 106 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def readFlagMode (bit : Bool) : Fin 45 := if bit then 8 else 7
def move3Mode (bit : Bool) : Fin 45 := if bit then 17 else 9
def move2Mode (bit : Bool) : Fin 45 := if bit then 18 else 10
def move1Mode (bit : Bool) : Fin 45 := if bit then 19 else 11
def writeMode (bit : Bool) : Fin 45 := if bit then 20 else 12

/-- One charged copy iteration. x,y,z are the actual three dead gap cells;
they are never supplied to the program or used as a certificate. -/
def copyUnit (saved bit x y z : Bool) (left tail : List Bool) : List (MachineState 106) :=
  [state (post saved 6) (x :: y :: z :: left) (bit :: true :: tail),
    state (post saved (readFlagMode bit)) (bit :: x :: y :: z :: left) (true :: tail),
    state (post saved (move3Mode bit)) (x :: y :: z :: left) (bit :: true :: tail),
    state (post saved (move2Mode bit)) (y :: z :: left) (x :: bit :: true :: tail),
    state (post saved (move1Mode bit)) (z :: left) (y :: x :: bit :: true :: tail),
    state (post saved (writeMode bit)) left (z :: y :: x :: bit :: true :: tail),
    state (post saved 13) left (bit :: y :: x :: bit :: true :: tail),
    state (post saved 14) (bit :: left) (y :: x :: bit :: true :: tail),
    state (post saved 15) (bit :: left) (true :: x :: bit :: true :: tail),
    state (post saved 16) (true :: bit :: left) (x :: bit :: true :: tail),
    state (post saved 21) (x :: true :: bit :: left) (bit :: true :: tail),
    state (post saved 22) (bit :: x :: true :: bit :: left) (true :: tail)]

theorem copyUnit_length (saved bit x y z : Bool) (left tail : List Bool) :
    (copyUnit saved bit x y z left tail).length = 12 := rfl

theorem copyUnit_head (saved bit x y z : Bool) (left tail : List Bool) :
    (copyUnit saved bit x y z left tail).head? =
      some (state (post saved 6) (x :: y :: z :: left) (bit :: true :: tail)) := rfl

theorem copyUnit_last (saved bit x y z : Bool) (left tail : List Bool) :
    (copyUnit saved bit x y z left tail).getLast? =
      some (state (post saved 22) (bit :: x :: true :: bit :: left) (true :: tail)) := rfl

/-- Eleven genuine within-iteration transitions; final advance is separate
because the caller immediately continues at the next input cell. -/
theorem copyUnit_chain (saved bit x y z : Bool) (left tail : List Bool) :
    (copyUnit saved bit x y z left tail).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  cases saved <;> cases bit <;>
    simp [copyUnit, List.isChain_cons_cons, post, readFlagMode, move3Mode, move2Mode,
      move1Mode, writeMode, Turing.TM0.step, paddedNatMachine, state, Turing.Tape.mk₂]

theorem copyUnit_advance (saved bit x : Bool) (left tail : List Bool) :
    Turing.TM0.step paddedNatMachine
      (state (post saved 22) (bit :: x :: true :: bit :: left) (true :: tail)) =
      some (state (post saved 6) (true :: bit :: x :: true :: bit :: left) tail) := by
  cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state, Turing.Tape.mk₂]

theorem padded_halt (saved : Bool) (left right : List Bool) :
    Turing.TM0.step paddedNatMachine (state (post saved 44) left right) = none := by
  cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state]

/-- Save the actual first suffix bit in finite control and install10.
For empty suffix, the later whole-tape proof uses the real blank first bit. -/
def markSuffix (first : Bool) (left rest : List Bool) : List (MachineState 106) :=
  [state 0 left (false :: first :: rest),
    state (post false 0) (false :: left) (first :: rest),
    state (post first 1) (false :: left) (false :: rest),
    state (post first 2) left (false :: false :: rest),
    state (post first 3) left (true :: false :: rest)]

theorem markSuffix_length (first : Bool) (left rest : List Bool) :
    (markSuffix first left rest).length = 5 := rfl

theorem markSuffix_chain (first : Bool) (left rest : List Bool) :
    (markSuffix first left rest).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  cases first <;> simp [markSuffix, List.isChain_cons_cons, post, Turing.TM0.step,
    paddedNatMachine, state, Turing.Tape.mk₂]

def rewindOldInitial (saved : Bool) : List Bool → List Bool → MachineState 106
  | [], right => state (post saved 4) [] (false :: right)
  | bit :: previous, right =>
    state (post saved 4) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

def rewindOld (saved : Bool) : List Bool → List Bool → List (MachineState 106)
  | [], right => [state (post saved 4) [] (false :: right), state (post saved 6) [false] right]
  | bit :: previous, right =>
    state (post saved 4) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state (post saved 5) (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) ::
      rewindOld saved previous (bit :: true :: right)

theorem rewindOld_head (saved : Bool) (previous right : List Bool) :
    (rewindOld saved previous right).head? = some (rewindOldInitial saved previous right) := by
  cases previous <;> rfl

theorem rewindOld_length (saved : Bool) (previous right : List Bool) :
    (rewindOld saved previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have h := ih (bit :: true :: right)
    change (rewindOld saved previous (bit :: true :: right)).length + 1 + 1 = 2 * (previous.length + 1) + 2
    omega

theorem rewindOld_chain (saved : Bool) (previous right : List Bool) :
    (rewindOld saved previous right).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  induction previous generalizing right with
  | nil =>
    cases saved <;> simp [rewindOld, List.isChain_cons_cons, Turing.TM0.step,
      paddedNatMachine, post, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindOld]
    apply List.isChain_cons_cons.mpr
    constructor
    · cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewindOld_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> cases saved <;>
        simp [rewindOldInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
          paddedNatMachine, post, state, Turing.Tape.mk₂]
    · exact ih _

theorem rewindOld_last (saved : Bool) (previous right : List Bool) :
    (rewindOld saved previous right).getLast? = some
      (state (post saved 6) [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindOld saved previous (bit :: true :: right) ≠ [] := by
      have hlen := rewindOld_length saved previous (bit :: true :: right)
      intro h
      simp [h] at hlen
    simp only [rewindOld, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPaddedNat012


