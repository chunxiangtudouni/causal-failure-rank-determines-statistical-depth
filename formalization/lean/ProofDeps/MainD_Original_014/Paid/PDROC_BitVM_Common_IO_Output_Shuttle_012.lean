module

public import Paid.PDROC_BitVM_Common_IO_Output_Write_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def fullArchive (below : List Bool) (cursor : RowTail) (above : List RowTail) : List Bool :=
  (flatRows above).reverse ++ (rowBits true cursor).reverse ++ below

def guardTape (below : List Bool) (cursor : RowTail) (above : List RowTail) (emitted : List Bool) : Tape Bool :=
  Tape.mk₂ (false :: true :: fullArchive below cursor above) (false :: PSTRTMIncrement009.blocks emitted)

def cursorTape (below : List Bool) (cursor : RowTail) (above : List RowTail) (emitted : List Bool) : Tape Bool :=
  Tape.mk₂ below (rowBits true cursor ++ flatRows above ++
    true :: false :: false :: PSTRTMIncrement009.blocks emitted)

/-- Genuine LEFT67 plus the entire real LEFT65 source-row search. No
old field is discarded: the exact whole archive is merely traversed. -/
theorem guard_to_cursor_path (saved : Store) (below : List Bool) (cursor : RowTail)
    (above : List RowTail) (emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 5 saved (guardTape below cursor above emitted))
      (cfg 7 saved (cursorTape below cursor above emitted)),
      path.posts.length = above.length + 2 := by
  cases reversed : above.reverse with
  | nil =>
    have shape : above = [] := by
      have same := congrArg List.reverse reversed
      simpa using same
    subst above
    let front := false :: true :: (rowBits true cursor).reverse
    have width : front.length = 67 := by simp [front, rowBits_length]
    have returned : TM1.step program (cfg 5 saved (guardTape below cursor [] emitted)) =
        some (cfg 6 saved (cursorTape below cursor [] emitted)) := by
      simpa [guardTape, cursorTape, fullArchive, flatRows, front, List.reverse_cons,
        List.append_assoc] using guard_return_step saved front below
          (PSTRTMIncrement009.blocks emitted) width
    have found : TM1.step program (cfg 6 saved (cursorTape below cursor [] emitted)) =
        some (cfg 7 saved (cursorTape below cursor [] emitted)) := by
      simpa [cursorTape, flatRows, rowBits] using
        source_found_step saved below (cursor.toList ++ true :: false :: false :: PSTRTMIncrement009.blocks emitted)
    refine ⟨(ActualPath.single returned).trans (ActualPath.single found), ?_⟩
    rfl
  | cons last reversePrefix =>
    have shape : above = reversePrefix.reverse ++ [last] := by
      have same := congrArg List.reverse reversed
      simpa using same
    let upperRows := reversePrefix.reverse
    let front := false :: true :: (rowBits false last).reverse
    let left := (flatRows upperRows).reverse ++ (rowBits true cursor).reverse ++ below
    let suffix := last.toList ++ true :: false :: false :: PSTRTMIncrement009.blocks emitted
    have width : front.length = 67 := by simp [front, rowBits_length]
    obtain ⟨⟨posts, chain, lastState⟩, length⟩ :=
      source_cursor_path saved reversePrefix cursor below suffix
    have lengthBound : posts.length = reversePrefix.length + 2 := length
    have returned : TM1.step program (cfg 5 saved (guardTape below cursor above emitted)) =
        some (cfg 6 saved (Tape.mk₂ left (false :: suffix))) := by
      simpa [guardTape, fullArchive, shape, upperRows, front, left, suffix, flatRows, rowBits,
        List.flatMap_append, List.reverse_append, List.append_assoc] using
        guard_return_step saved front left (PSTRTMIncrement009.blocks emitted) width
    let later : ActualPath (TM1.step program)
        (cfg 6 saved (Tape.mk₂ left (false :: suffix)))
        (cfg 7 saved (cursorTape below cursor above emitted)) :=
      ⟨posts,
        by simpa [left, upperRows, List.append_assoc] using chain,
        by simpa [cursorTape, shape, upperRows, left, suffix, flatRows, rowBits,
          List.flatMap_append, List.append_assoc] using lastState⟩
    refine ⟨(ActualPath.single returned).trans later, ?_⟩
    simp only [ActualPath.trans, ActualPath.single, later, List.length_append, List.length_cons, List.length_nil]
    simp only [shape, List.length_append, List.length_reverse, List.length_cons, List.length_nil]
    omega

/-- One complete actual source-bit shuttle from the first output flag:
find endflag, write the real saved bit, scan back to guard, return across
ALL oldGamma rows to the SAME source cursor, retaining every other cell. -/
theorem one_bit_return_path (saved : Store) (below : List Bool) (cursor : RowTail)
    (above : List RowTail) (emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 4 saved (readyTape (fullArchive below cursor above) emitted))
      (cfg 7 saved (cursorTape below cursor above (emitted ++ [saved.bit]))),
      path.posts.length = above.length + 2 * emitted.length + 4 := by
  obtain ⟨first, firstLength⟩ := write_guard_path saved (fullArchive below cursor above) emitted
  obtain ⟨second, secondLength⟩ := guard_to_cursor_path saved below cursor above (emitted ++ [saved.bit])
  let joined := first.trans second
  refine ⟨joined, ?_⟩
  simp only [joined, ActualPath.trans, List.length_append]
  omega

end PDROC.BitVM.Common.IO.Output
