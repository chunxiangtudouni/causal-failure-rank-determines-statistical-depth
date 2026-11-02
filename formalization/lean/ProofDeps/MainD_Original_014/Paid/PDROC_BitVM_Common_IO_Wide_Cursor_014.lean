module

public import Paid.PDROC_BitVM_Common_IO_Wide_Fixed_013
public import Paid.PDROC_BitVM_Common_IO_Wide_CleanupPath_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

theorem cursor_fixed_path (saved : Store) (done word suffix : List Bool)
    (wordLength : saved.remaining.val = word.length) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (cursorState 1 saved done (word ++ suffix))
      (cursorState 2 final (done ++ word) suffix),
      final.field = saved.field ∧ final.remaining = 0 ∧
      path.posts.length ≤ fixedCost word.length (done.length + 1) done.length := by
  obtain ⟨final, ⟨posts, chain, last⟩, field, remaining, bound⟩ :=
    fixed_word_path saved (done.length + 1) done word suffix wordLength
  refine ⟨final, ⟨posts, ?_, ?_⟩, field, remaining, bound⟩
  · simpa [cursorState, state] using chain
  · simpa [cursorState, state, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last

theorem cursor_nat_path (saved : Store) (done digits suffix : List Bool) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (cursorState 2 saved done (rawField digits ++ suffix))
      (cursorState 4 final (done ++ rawField digits) suffix),
      final.field = saved.field ∧ final.remaining = saved.remaining ∧
      final.marked = false ∧ final.next = 4 ∧
      path.posts.length ≤ natFieldCost digits.length (done.length + 1) done.length := by
  obtain ⟨final, ⟨posts, chain, last⟩, field, remaining, marked, next, bound⟩ :=
    nat_field_path saved (done.length + 1) done digits suffix
  refine ⟨final, ⟨posts, ?_, ?_⟩, field, remaining, marked, next, bound⟩
  · simpa [cursorState, state] using chain
  · simpa [cursorState, state, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last

def advanceStore (saved : Store) : Store :=
  { saved with field := PDROC.BitVM.Common.IO.Bootstrap.followingField saved.field, remaining := PDROC.BitVM.Common.IO.Bootstrap.followingSkip saved.field }

/-- The field counter is a real finite-control load; source and output
rows remain exactly the same at this actual transition. -/
theorem advance_field_step (saved : Store) (notLast : saved.field.val ≠ 9)
    (left right : List Bool) :
    TM1.step program (state 4 saved left right) = some (state 1 (advanceStore saved) left right) := by
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program,
    state, advanceStore, notLast]

def footerStore (saved : Store) : Store := { saved with marked := false, next := 5 }

theorem footer_step (saved : Store) (lastField : saved.field.val = 9) (left right : List Bool) :
    TM1.step program (state 4 saved left right) = some (state 9 (footerStore saved) left right) := by
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program,
    state, footerStore, lastField]

def footerReadStore (saved : Store) : Store := { footerStore saved with bit := true }

/-- The sole original footer is read and emitted by the same real
65-cell row writer. The remaining TRUE is the actual cursor, not another
source bit and not another decoded output cell. -/
theorem cursor_footer_path (saved : Store) (lastField : saved.field.val = 9) (done : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cursorState 4 saved done [true])
      (cursorState 14 (footerReadStore saved) (done ++ [true]) []),
      path.posts.length ≤ 4 * done.length + 10 := by
  obtain ⟨⟨posts, chain, last⟩, bound⟩ :=
    program_emit_one_bit (footerStore saved) true (done.length + 1) (unmarkedRows done) []
  have count : posts.length ≤ 4 * done.length + 9 := by
    have localBound : posts.length ≤ 2 * (done.length + 1) + 2 * done.length + 7 := by
      simpa [unmarkedRows] using bound
    omega
  let later : ActualPath (TM1.step program)
      (cursorState 9 (footerStore saved) done [true])
      (cursorState 14 (footerReadStore saved) (done ++ [true]) []) :=
    ⟨posts, by simpa [cursorState, state] using chain,
      by simpa [cursorState, state, footerReadStore, footerStore, unmarkedRows,
        List.map_append, List.length_append, PDROC.BitVM.Common.IO.Bootstrap.dispatch,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
  have edge : TM1.step program (cursorState 4 saved done [true]) =
      some (cursorState 9 (footerStore saved) done [true]) := footer_step saved lastField _ _
  refine ⟨(ActualPath.single edge).trans later, ?_⟩
  simp only [ActualPath.trans, ActualPath.single, later, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Original footer emission followed by genuine cursor/anchor/mark
erasure and real HALT, retaining WHOLE tape equality to the Fin32 codec. -/
theorem cursor_finish_path (saved : Store) (lastField : saved.field.val = 9) (done : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cursorState 4 saved done [true])
      (⟨none, footerReadStore saved, Tape.mk₁ (encodedInit32 (done ++ [true]))⟩ : TM1.Cfg Bool Label Store),
      path.posts.length ≤ 8 * done.length + 19 := by
  obtain ⟨first, firstBound⟩ := cursor_footer_path saved lastField done
  obtain ⟨⟨posts, chain, last⟩, bound⟩ :=
    complete_cleanup_path (footerReadStore saved) (done.length + 2) (unmarkedRows done) true false
  have count : posts.length ≤ 4 * done.length + 9 := by
    have localBound : posts.length ≤ (done.length + 2) + 3 * done.length + 7 := by
      simpa [unmarkedRows] using bound
    omega
  let later : ActualPath (TM1.step program)
      (cursorState 14 (footerReadStore saved) (done ++ [true]) [])
      (⟨none, footerReadStore saved, Tape.mk₁ (encodedInit32 (done ++ [true]))⟩ : TM1.Cfg Bool Label Store) :=
    ⟨posts,
      by simpa [cursorState, state, unmarkedRows, List.map_append, List.length_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain,
      by simpa [cursorState, state, unmarkedRows, List.map_append, List.length_append,
        List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
  refine ⟨first.trans later, ?_⟩
  simp only [ActualPath.trans, later, List.length_append]
  omega

end PDROC.BitVM.Common.IO.Wide
