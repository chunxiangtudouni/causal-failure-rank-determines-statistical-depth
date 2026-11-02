module
public import Common.PSTR_TM_PaddedNat_012

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPaddingTrace014
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMPaddedNat012

def rewindNewInitial (saved : Bool) : List Bool → List Bool → MachineState 106
  | [], right => state (post saved 42) [] (false :: right)
  | bit :: previous, right =>
    state (post saved 42) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right)

def rewindNew (saved : Bool) : List Bool → List Bool → List (MachineState 106)
  | [], right => [state (post saved 42) [] (false :: right), state (post saved 44) [false] right]
  | bit :: previous, right =>
    state (post saved 42) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state (post saved 43) (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) ::
      rewindNew saved previous (bit :: true :: right)

theorem rewindNew_head (saved : Bool) (previous right : List Bool) :
    (rewindNew saved previous right).head? = some (rewindNewInitial saved previous right) := by
  cases previous <;> rfl

theorem rewindNew_length (saved : Bool) (previous right : List Bool) :
    (rewindNew saved previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have h := ih (bit :: true :: right)
    change (rewindNew saved previous (bit :: true :: right)).length + 1 + 1 = 2 * (previous.length + 1) + 2
    omega

theorem rewindNew_chain (saved : Bool) (previous right : List Bool) :
    (rewindNew saved previous right).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  induction previous generalizing right with
  | nil => cases saved <;> simp [rewindNew, List.isChain_cons_cons, Turing.TM0.step,
      paddedNatMachine, post, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [rewindNew]
    apply List.isChain_cons_cons.mpr
    constructor
    · cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewindNew_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> cases saved <;>
        simp [rewindNewInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
          paddedNatMachine, post, state, Turing.Tape.mk₂]
    · exact ih _

theorem rewindNew_last (saved : Bool) (previous right : List Bool) :
    (rewindNew saved previous right).getLast? = some
      (state (post saved 44) [false] (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : rewindNew saved previous (bit :: true :: right) ≠ [] := by
      have hlen := rewindNew_length saved previous (bit :: true :: right)
      intro h
      simp [h] at hlen
    simp only [rewindNew, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- Install OWN00 plus permanentEnd10, restore the public suffix-first bit,
and position at the first pad cell before the final actual rewind. -/
def closePrefix (saved x y z : Bool) (left rest : List Bool) : List (MachineState 106) :=
  [state (post saved 6) (x :: y :: z :: left) (true :: false :: rest),
    state (post saved 8) (true :: x :: y :: z :: left) (false :: rest),
    state (post saved 25) (x :: y :: z :: left) (true :: false :: rest),
    state (post saved 26) (y :: z :: left) (x :: true :: false :: rest),
    state (post saved 27) (z :: left) (y :: x :: true :: false :: rest),
    state (post saved 28) left (z :: y :: x :: true :: false :: rest),
    state (post saved 29) left (false :: y :: x :: true :: false :: rest),
    state (post saved 30) (false :: left) (y :: x :: true :: false :: rest),
    state (post saved 31) (false :: left) (false :: x :: true :: false :: rest),
    state (post saved 32) (false :: false :: left) (x :: true :: false :: rest),
    state (post saved 33) (false :: false :: left) (true :: true :: false :: rest),
    state (post saved 34) (true :: false :: false :: left) (true :: false :: rest),
    state (post saved 35) (true :: false :: false :: left) (false :: false :: rest),
    state (post saved 36) (false :: true :: false :: false :: left) (false :: rest),
    state (post saved 37) (false :: true :: false :: false :: left) (saved :: rest),
    state (post saved 38) (true :: false :: false :: left) (false :: saved :: rest),
    state (post saved 39) (false :: false :: left) (true :: false :: saved :: rest),
    state (post saved 40) (false :: left) (false :: true :: false :: saved :: rest),
    state (post saved 41) left (false :: false :: true :: false :: saved :: rest)]

theorem closePrefix_head (saved x y z : Bool) (left rest : List Bool) :
    (closePrefix saved x y z left rest).head? =
      some (state (post saved 6) (x :: y :: z :: left) (true :: false :: rest)) := rfl

theorem closePrefix_last (saved x y z : Bool) (left rest : List Bool) :
    (closePrefix saved x y z left rest).getLast? =
      some (state (post saved 41) left (false :: false :: true :: false :: saved :: rest)) := rfl

theorem closePrefix_length (saved x y z : Bool) (left rest : List Bool) :
    (closePrefix saved x y z left rest).length = 19 := rfl

theorem closePrefix_chain (saved x y z : Bool) (left rest : List Bool) :
    (closePrefix saved x y z left rest).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  cases saved <;> simp [closePrefix, List.isChain_cons_cons, Turing.TM0.step,
    paddedNatMachine, post, state, Turing.Tape.mk₂]

def copyLoop (saved : Bool) (previous : List Bool) : List Bool → Bool → Bool → Bool → List Bool → List (MachineState 106)
  | [], x, y, z, rest => closePrefix saved x y z (PSTRTMRawNat010.leftBlocks previous) rest ++
    rewindNew saved previous (false :: false :: true :: false :: saved :: rest)
  | bit :: later, x, y, z, rest =>
    copyUnit saved bit x y z (PSTRTMRawNat010.leftBlocks previous)
      (PSTRTMIncrement009.blocks later ++ true :: false :: rest) ++
        copyLoop saved (bit :: previous) later true bit x rest

theorem copyLoop_head (saved : Bool) (previous digits : List Bool) (x y z : Bool) (rest : List Bool) :
    (copyLoop saved previous digits x y z rest).head? = some
      (state (post saved 6) (x :: y :: z :: PSTRTMRawNat010.leftBlocks previous)
        (PSTRTMIncrement009.blocks digits ++ true :: false :: rest)) := by
  cases digits with
  | nil => simp [copyLoop, List.head?_append, closePrefix_head, PSTRTMIncrement009.blocks]
  | cons bit later => simp [copyLoop, List.head?_append, copyUnit_head, PSTRTMIncrement009.blocks]

theorem copyLoop_length (saved : Bool) (previous digits : List Bool) (x y z : Bool) (rest : List Bool) :
    (copyLoop saved previous digits x y z rest).length = 2 * previous.length + 14 * digits.length + 21 := by
  induction digits generalizing previous x y z with
  | nil => simp only [copyLoop, List.length_append, closePrefix_length, rewindNew_length, List.length_nil]; omega
  | cons bit later ih =>
    simp only [copyLoop, List.length_append, copyUnit_length, ih, List.length_cons]
    omega

theorem copyLoop_last (saved : Bool) (previous digits : List Bool) (x y z : Bool) (rest : List Bool) :
    (copyLoop saved previous digits x y z rest).getLast? = some
      (state (post saved 44) [false]
        (PSTRTMIncrement009.blocks (previous.reverse ++ digits) ++ false :: false :: true :: false :: saved :: rest)) := by
  induction digits generalizing previous x y z with
  | nil => simp [copyLoop, List.getLast?_append, rewindNew_last]
  | cons bit later ih =>
    simp [copyLoop, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

private theorem append_link (xs ys : List (MachineState 106)) (last first : MachineState 106)
    (hx : xs.IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step paddedNatMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem copyLoop_chain (saved : Bool) (previous digits : List Bool) (x y z : Bool) (rest : List Bool) :
    (copyLoop saved previous digits x y z rest).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  induction digits generalizing previous x y z with
  | nil =>
    rw [copyLoop]
    apply append_link _ _ _ _ (closePrefix_chain saved x y z _ rest) (rewindNew_chain saved previous _)
      (closePrefix_last saved x y z _ rest) (rewindNew_head saved previous _)
    cases previous <;> cases saved <;>
      simp [rewindNewInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
        paddedNatMachine, post, state, Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [copyLoop]
    apply append_link _ _ _ _ (copyUnit_chain saved bit x y z _ _)
      (ih (bit :: previous) true bit x) (copyUnit_last saved bit x y z _ _)
      (copyLoop_head saved (bit :: previous) later true bit x rest)
    simpa only [PSTRTMRawNat010.leftBlocks, List.flatMap_cons, List.cons_append, List.nil_append]
      using copyUnit_advance saved bit x (PSTRTMRawNat010.leftBlocks previous)
        (PSTRTMIncrement009.blocks later ++ true :: false :: rest)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPaddingTrace014
