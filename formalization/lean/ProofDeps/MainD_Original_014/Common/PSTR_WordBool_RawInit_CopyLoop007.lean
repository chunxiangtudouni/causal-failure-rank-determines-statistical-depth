module

public import Common.PSTR_WordBool_RawInit_CopyRound006

/-! The real fixed-table header copier continues until its actual left
separator, then traverses the restored work flags back to the temporarily
saved unread head. Original and bank digit lists agree in the complete
final tape; their lengths are not an input or a loop-fuel parameter. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009

def coreFinal (digits tail : List Bool) : MachineState 41 :=
  coreState 5 (false :: (bank digits ++ false :: false :: bank digits)) (false :: tail)

def exitTrace (copied tail : List Bool) : List (MachineState 41) :=
  [loopStart [] copied tail] ++
    rightTrace 2 false (false :: false :: bank copied) copied false tail

theorem exit_head (copied tail : List Bool) :
    (exitTrace copied tail).head? = some (loopStart [] copied tail) := rfl

theorem exit_last (copied tail : List Bool) :
    (exitTrace copied tail).getLast? = some (coreFinal copied tail) := by
  have app := List.getLast?_append (l := [loopStart [] copied tail])
    (l' := rightTrace 2 false (false :: false :: bank copied) copied false tail)
  rw [right_last, Option.some_or] at app
  exact app

theorem exit_length (copied tail : List Bool) :
    (exitTrace copied tail).length = 2 * copied.length + 3 := by
  change (rightTrace 2 false (false :: false :: bank copied) copied false tail).length + 1 = _
  rw [right_length]

theorem exit_chain (copied tail : List Bool) :
    (exitTrace copied tail).IsChain (fun before after => TM0.step coreMachine before = some after) := by
  change (loopStart [] copied tail ::
    rightTrace 2 false (false :: false :: bank copied) copied false tail).IsChain _
  apply List.isChain_cons.mpr
  constructor
  · intro next nextHead
    simp only [right_head, Option.mem_some_iff] at nextHead
    subst next
    simp [loopStart, workRight, rightData, coreState, TM0.step, coreMachine, Tape.mk₂]
  · exact right_chain 2 false false (false :: false :: bank copied) copied tail

theorem core_final_halt (digits tail : List Bool) :
    TM0.step coreMachine (coreFinal digits tail) = none := by
  simp [coreFinal, coreState, TM0.step, coreMachine, Tape.mk₂]

def loopTrace : List Bool → List Bool → List Bool → List (MachineState 41)
  | [], copied, tail => exitTrace copied tail
  | bit :: lower, copied, tail =>
    roundTrace bit lower copied tail ++ loopTrace lower (bit :: copied) tail

theorem loop_head (remaining copied tail : List Bool) :
    (loopTrace remaining copied tail).head? = some (loopStart remaining copied tail) := by
  cases remaining with
  | nil => exact exit_head copied tail
  | cons bit lower =>
    have app := List.head?_append (l := roundTrace bit lower copied tail) (l' := loopTrace lower (bit :: copied) tail)
    rw [round_head, Option.some_or] at app
    exact app

theorem loop_last (remaining copied tail : List Bool) :
    (loopTrace remaining copied tail).getLast? = some (coreFinal (remaining.reverse ++ copied) tail) := by
  induction remaining generalizing copied with
  | nil => exact exit_last copied tail
  | cons bit lower ih =>
    have app := List.getLast?_append (l := roundTrace bit lower copied tail) (l' := loopTrace lower (bit :: copied) tail)
    rw [ih, Option.some_or] at app
    simpa only [loopTrace, List.reverse_cons, List.append_assoc, List.singleton_append] using app

theorem loop_length (remaining copied tail : List Bool) :
    (loopTrace remaining copied tail).length =
      remaining.length * (4 * (remaining.length + copied.length) + 14) +
        2 * (remaining.length + copied.length) + 3 := by
  induction remaining generalizing copied with
  | nil => simpa only [loopTrace, List.length_nil, Nat.zero_mul, Nat.zero_add] using exit_length copied tail
  | cons bit lower ih =>
    simp only [loopTrace, List.length_append, round_length, ih, List.length_cons]
    ring

theorem loop_chain (remaining copied tail : List Bool) :
    (loopTrace remaining copied tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  induction remaining generalizing copied with
  | nil => exact exit_chain copied tail
  | cons bit lower ih =>
    change (roundTrace bit lower copied tail ++ loopTrace lower (bit :: copied) tail).IsChain _
    apply List.IsChain.append (round_chain bit lower copied tail) (ih _)
    intro before beforeLast after afterHead
    simp only [round_last, Option.mem_some_iff] at beforeLast
    simp only [loop_head, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact round_next bit lower copied tail

end PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy
