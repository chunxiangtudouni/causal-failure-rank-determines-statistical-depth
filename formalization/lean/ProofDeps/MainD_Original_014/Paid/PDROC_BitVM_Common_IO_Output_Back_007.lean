module

public import Paid.PDROC_BitVM_Common_IO_Output_Source_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

/-- Nearest old row first. Only the final col0 is the actual TRUE
source cursor; the arbitrary intervening row contents are retained. -/
def sourceLeft : List RowTail → List Bool
  | [] => []
  | tail :: rest => (rowBits rest.isEmpty tail).reverse ++ sourceLeft rest

def sourceBackFrame (saved : Store) (rows : List RowTail) (left suffix : List Bool) : TM1.Cfg Bool Label Store :=
  match rows with
  | [] => cfg 6 saved (Tape.mk₂ left (true :: suffix))
  | _ :: _ => cfg 6 saved (Tape.mk₂ (sourceLeft rows ++ left) (false :: suffix))

def sourceRight : List RowTail → List Bool → List Bool
  | [], suffix => true :: suffix
  | tail :: rest, suffix => sourceRight rest (tail.toList ++ false :: suffix)

theorem sourceBackFrame_nonempty (saved : Store) (rows : List RowTail) (left suffix : List Bool)
    (nonempty : rows ≠ []) :
    sourceBackFrame saved rows left suffix = cfg 6 saved (Tape.mk₂ (sourceLeft rows ++ left) (false :: suffix)) := by
  cases rows with
  | nil => exact False.elim (nonempty rfl)
  | cons tail rows => rfl

theorem source_back_edge (saved : Store) (tail : RowTail) (rows : List RowTail) (left suffix : List Bool) :
    TM1.step program (sourceBackFrame saved (tail :: rows) left suffix) =
      some (sourceBackFrame saved rows left (tail.toList ++ false :: suffix)) := by
  cases rows with
  | nil =>
    simpa [sourceBackFrame, sourceLeft, rowBits] using source_back_step saved true tail left suffix
  | cons previous rest =>
    simpa [sourceBackFrame, sourceLeft, rowBits, List.append_assoc] using
      source_back_step saved false tail (sourceLeft (previous :: rest) ++ left) suffix

/-- Complete real LEFT65 row search, then the actual cursor-found
transition. All readonly/register/heap contents remain in the SAME tape;
the proof list is never a program input, counter, alphabet or Store. -/
theorem source_back_path (saved : Store) (rows : List RowTail) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (sourceBackFrame saved rows left suffix)
      (cfg 7 saved (Tape.mk₂ left (sourceRight rows suffix))),
      path.posts.length = rows.length + 1 := by
  induction rows generalizing suffix with
  | nil => exact ⟨ActualPath.single (source_found_step saved left suffix), rfl⟩
  | cons tail rows ih =>
    have edge := source_back_edge saved tail rows left suffix
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih (tail.toList ++ false :: suffix)
    have lengthBound : posts.length = rows.length + 1 := length
    let later : ActualPath (TM1.step program)
        (sourceBackFrame saved rows left (tail.toList ++ false :: suffix))
        (cfg 7 saved (Tape.mk₂ left (sourceRight (tail :: rows) suffix))) := ⟨posts, chain, last⟩
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans, ActualPath.single, later, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Explicit endpoint for a real cursor row, retaining every old row
between that cursor and the endAnchor in its original physical order. -/
theorem sourceRight_cursor (rows : List RowTail) (cursor : RowTail) (suffix : List Bool) :
    sourceRight (rows ++ [cursor]) suffix =
      rowBits true cursor ++ flatRows rows.reverse ++ false :: suffix := by
  induction rows generalizing suffix with
  | nil => simp [sourceRight, rowBits, flatRows]
  | cons tail rows ih =>
    simpa [sourceRight, rowBits, flatRows, List.reverse_cons, List.flatMap_append, List.append_assoc] using
      ih (tail.toList ++ false :: suffix)

theorem sourceLeft_cursor (rows : List RowTail) (cursor : RowTail) :
    sourceLeft (rows ++ [cursor]) =
      (flatRows rows.reverse).reverse ++ (rowBits true cursor).reverse := by
  induction rows with
  | nil => simp [sourceLeft, flatRows]
  | cons tail rows ih =>
    have marker : (rows ++ [cursor]).isEmpty = false := by simp
    simpa [sourceLeft, marker, flatRows, List.reverse_cons, List.flatMap_append, List.reverse_append,
      List.append_assoc] using congrArg ((rowBits false tail).reverse ++ ·) ih

/-- Same selected row-search witness in the literal cursor/archive
layout used by the shuttle. No alternative successful run is selected. -/
theorem source_cursor_path (saved : Store) (rows : List RowTail) (cursor : RowTail) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 6 saved (Tape.mk₂ ((flatRows rows.reverse).reverse ++ (rowBits true cursor).reverse ++ left)
        (false :: suffix)))
      (cfg 7 saved (Tape.mk₂ left (rowBits true cursor ++ flatRows rows.reverse ++ false :: suffix))),
      path.posts.length = rows.length + 2 := by
  obtain ⟨⟨posts, chain, last⟩, length⟩ := source_back_path saved (rows ++ [cursor]) left suffix
  have start := sourceBackFrame_nonempty saved (rows ++ [cursor]) left suffix (by simp)
  refine ⟨⟨posts, ?_, ?_⟩, ?_⟩
  · simpa only [start, sourceLeft_cursor, List.append_assoc] using chain
  · simpa only [start, sourceLeft_cursor, sourceRight_cursor, List.append_assoc] using last
  · simpa using length

end PDROC.BitVM.Common.IO.Output
