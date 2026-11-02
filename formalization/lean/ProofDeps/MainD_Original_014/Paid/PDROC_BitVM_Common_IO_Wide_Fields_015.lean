module

public import Paid.PDROC_BitVM_Common_IO_Wide_Cursor_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

/-- A specification of existing input cells, never a machine store or
an alphabet. The one checked program reads these bits from its tape. -/
structure FieldBlock where
  fixed : List Bool
  digits : List Bool

def blockWord (block : FieldBlock) : List Bool := block.fixed ++ rawField block.digits

def fieldsWord (blocks : List FieldBlock) : List Bool := blocks.flatMap blockWord

def blockCost (block : FieldBlock) (gap rows : Nat) : Nat :=
  fixedCost block.fixed.length gap rows +
    natFieldCost block.digits.length (gap + block.fixed.length) (rows + block.fixed.length)

def fieldsCost : List FieldBlock → Nat → Nat → Nat
  | [], _, _ => 0
  | block :: rest, gap, rows => blockCost block gap rows + 1 +
      fieldsCost rest (gap + (blockWord block).length) (rows + (blockWord block).length)

/-- Exact finite field-index and tag-length schedule. The first block's
fixed prefix is matched separately to the real incoming Fin9 counter. -/
def Scheduled (field : Fin 10) : List FieldBlock → Prop
  | [] => False
  | _ :: tail => match tail with
    | [] => field.val = 9
    | next :: rest => field.val ≠ 9 ∧
        next.fixed.length = (PDROC.BitVM.Common.IO.Bootstrap.followingSkip field).val ∧
        Scheduled (PDROC.BitVM.Common.IO.Bootstrap.followingField field) (next :: rest)

def CountMatches (saved : Store) : List FieldBlock → Prop
  | [] => False
  | block :: _ => saved.remaining.val = block.fixed.length

theorem cursor_block_path (block : FieldBlock) (saved : Store) (done suffix : List Bool)
    (count : saved.remaining.val = block.fixed.length) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (cursorState 1 saved done (blockWord block ++ suffix))
      (cursorState 4 final (done ++ blockWord block) suffix),
      final.field = saved.field ∧
      path.posts.length ≤ blockCost block (done.length + 1) done.length := by
  obtain ⟨middle, first, firstField, _, firstBound⟩ :=
    cursor_fixed_path saved done block.fixed (rawField block.digits ++ suffix) count
  obtain ⟨final, ⟨posts, chain, last⟩, field, _, _, _, bound⟩ :=
    cursor_nat_path middle (done ++ block.fixed) block.digits suffix
  have lengthBound : posts.length ≤
      natFieldCost block.digits.length (done.length + 1 + block.fixed.length)
        (done.length + block.fixed.length) := by
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
  let later : ActualPath (TM1.step program)
      (cursorState 2 middle (done ++ block.fixed) (rawField block.digits ++ suffix))
      (cursorState 4 final (done ++ blockWord block) suffix) :=
    ⟨posts, chain, by simpa [blockWord, List.append_assoc] using last⟩
  let joined := first.trans later
  refine ⟨final, ⟨joined.posts, ?_, ?_⟩, field.trans firstField, ?_⟩
  · simpa [blockWord, List.append_assoc] using joined.chain
  · simpa [blockWord, List.append_assoc] using joined.last
  · have count : joined.posts.length = first.posts.length + posts.length :=
      ActualPath.trans_length first later
    rw [count]
    exact Nat.add_le_add firstBound lengthBound

/-- The same real path processes every numeric field, actually executes
each finite field advance, and stops at field9 before the original footer.
No numeric width, intermediate encoded tape, or successful run is assumed. -/
theorem fields_path (blocks : List FieldBlock) (saved : Store) (done suffix : List Bool)
    (schedule : Scheduled saved.field blocks) (count : CountMatches saved blocks) :
    ∃ final : Store, ∃ path : ActualPath (TM1.step program)
      (cursorState 1 saved done (fieldsWord blocks ++ suffix))
      (cursorState 4 final (done ++ fieldsWord blocks) suffix),
      final.field.val = 9 ∧
      path.posts.length ≤ fieldsCost blocks (done.length + 1) done.length := by
  induction blocks generalizing saved done with
  | nil => exact False.elim schedule
  | cons block rest ih =>
    obtain ⟨middle, first, field, firstBound⟩ :=
      cursor_block_path block saved done (fieldsWord rest ++ suffix) count
    cases rest with
    | nil =>
      refine ⟨middle, ⟨first.posts, ?_, ?_⟩, ?_, ?_⟩
      · simpa [fieldsWord] using first.chain
      · simpa [fieldsWord] using first.last
      · exact (congrArg Fin.val field).trans schedule
      · simpa only [fieldsCost, Nat.add_zero] using Nat.le_succ_of_le firstBound
    | cons next rest =>
      obtain ⟨notLast, nextCount, nextSchedule⟩ := schedule
      have edge : TM1.step program (cursorState 4 middle (done ++ blockWord block)
          (fieldsWord (next :: rest) ++ suffix)) =
          some (cursorState 1 (advanceStore middle) (done ++ blockWord block)
            (fieldsWord (next :: rest) ++ suffix)) :=
        advance_field_step middle (by simpa only [field] using notLast) _ _
      have matched : CountMatches (advanceStore middle) (next :: rest) := by
        simpa only [CountMatches, advanceStore, field] using nextCount.symm
      have scheduled : Scheduled (advanceStore middle).field (next :: rest) := by
        simpa only [advanceStore, field] using nextSchedule
      obtain ⟨final, ⟨posts, chain, last⟩, finalField, bound⟩ :=
        ih (advanceStore middle) (done ++ blockWord block) scheduled matched
      have lengthBound : posts.length ≤ fieldsCost (next :: rest)
          (done.length + 1 + (blockWord block).length) (done.length + (blockWord block).length) := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
      let later : ActualPath (TM1.step program)
          (cursorState 1 (advanceStore middle) (done ++ blockWord block)
            (fieldsWord (next :: rest) ++ suffix))
          (cursorState 4 final (done ++ fieldsWord (block :: next :: rest)) suffix) :=
        ⟨posts, chain, by simpa [fieldsWord, List.append_assoc] using last⟩
      let joined := (first.trans (ActualPath.single edge)).trans later
      refine ⟨final, ⟨joined.posts, ?_, ?_⟩, finalField, ?_⟩
      · simpa [fieldsWord, List.append_assoc] using joined.chain
      · simpa [fieldsWord, List.append_assoc] using joined.last
      · have count : joined.posts.length = first.posts.length + 1 + posts.length := by
          simp only [joined, ActualPath.trans, ActualPath.single, later,
            List.length_append, List.length_cons, List.length_nil]
        rw [count]
        exact Nat.add_le_add (Nat.add_le_add_right firstBound 1) lengthBound

end PDROC.BitVM.Common.IO.Wide
