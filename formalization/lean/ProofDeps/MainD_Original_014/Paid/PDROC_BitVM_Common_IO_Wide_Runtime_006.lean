module

public import Paid.PDROC_BitVM_Common_IO_Wide_Program_004
public import Paid.PDROC_BitVM_Common_IO_Wide_Paths_005

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

/-- Semantic summaries of the already explicit primitive code. These
proof-only tape expressions do not supply transitions or free movement;
SupportClock charges every move/write in moveCode/writeBackCode. -/
theorem moveCode_semantics {Control Storage : Type*} (direction : Dir) (count : Nat)
    (next : TM1.Stmt Bool Control Storage) (saved : Storage) (tape : Tape Bool) :
    TM1.stepAux (moveCode direction count next) saved tape =
      TM1.stepAux next saved ((fun old : Tape Bool => old.move direction)^[count] tape) := by
  induction count generalizing tape with
  | zero => rfl
  | succ count ih =>
    simpa only [moveCode, TM1.stepAux, Function.iterate_succ_apply] using ih (tape.move direction)

def writtenTape : List Bool → Tape Bool → Tape Bool
  | [], tape => tape.move .right
  | bit :: bits, tape => writtenTape bits ((tape.write bit).move .left)

theorem writeBackCode_semantics {Control Storage : Type*} (values : List (Storage → Bool))
    (next : TM1.Stmt Bool Control Storage) (saved : Storage) (tape : Tape Bool) :
    TM1.stepAux (writeBackCode values next) saved tape =
      TM1.stepAux next saved (writtenTape (values.map (fun getter => getter saved)) tape) := by
  induction values generalizing tape with
  | nil => rfl
  | cons getter values ih =>
    simpa only [writeBackCode, TM1.stepAux, List.map_cons, writtenTape] using
      ih ((tape.write (getter saved)).move .left)

theorem framed_getter_values (context : Store) (saved : Bool) :
    runtimeGetters.map (fun getter => getter { context with bit := saved }) =
      (outputGetters 29 context.marked).map (fun getter => getter saved) := by
  apply List.reverse_inj.mp
  exact (runtimeGetters_value { context with bit := saved }).trans (outputGetters_value 29 context.marked saved).symm

def emitLabel (context : Store) (label : EmitLabel) : Label :=
  match label.val with
  | 0 => 9
  | 1 => 10
  | 2 => 11
  | 3 => 12
  | 4 => 13
  | _ => PDROC.BitVM.Common.IO.Bootstrap.dispatch context.next

def embedEmit (context : Store) (state : EmitState) : TM1.Cfg Bool Label Store :=
  ⟨state.l.map (emitLabel context), { context with bit := state.var }, state.Tape⟩

/-- The literal final Fin32 caller executes the same physical row macro.
Its finite field/remaining/mark/continuation store stays with the caller. -/
theorem embed_emit_step (context : Store) (label : EmitLabel) (active : label.val < 5)
    (saved : Bool) (tape : Tape Bool) :
    TM1.step program (embedEmit context ⟨some label, saved, tape⟩) =
      (TM1.step (emitProgram 29 context.marked) ⟨some label, saved, tape⟩).map (embedEmit context) := by
  fin_cases label
  all_goals simp at active
  all_goals first
    | rfl
    | (cases h : tape.head <;>
        simp [embedEmit, emitLabel, TM1.step, TM1.stepAux, program,
          PDROC.BitVM.Common.IO.Bootstrap.program, emitProgram, writeTemporary65,
          moveCode_semantics, writeBackCode_semantics, framed_getter_values, stride, h])

theorem emit_path_live (marked : Bool) (before after : EmitState)
    (path : EmitPath 29 marked before after) (live : after.l ≠ none) :
    ∀ state ∈ before :: path.posts, state.l ≠ none := by
  apply path.chain.backwards_induction (fun state => state.l ≠ none) (before :: path.posts)
  · intro old next edge _ absent
    cases old with
    | mk label saved tape =>
      simp only at absent
      subst label
      cases edge
  · intro nonempty
    have same : (before :: path.posts).getLast nonempty = after :=
      (List.getLast_eq_iff_getLast?_eq_some nonempty).mpr path.last
    rw [same]
    exact live

theorem embed_emit_edge (context : Store) (before after : EmitState)
    (edge : TM1.step (emitProgram 29 context.marked) before = some after)
    (afterLive : after.l ≠ none) :
    TM1.step program (embedEmit context before) = some (embedEmit context after) := by
  cases before with
  | mk label saved tape =>
    cases label with
    | none => cases edge
    | some label =>
      have active : label.val < 5 := by
        by_contra inactive
        have finalLabel : label = 5 := Fin.ext (by have safe := label.isLt; omega)
        subst label
        have equal : (⟨none, saved, tape⟩ : EmitState) = after := Option.some.inj edge
        exact afterLive ((congrArg TM1.Cfg.l equal).symm)
      rw [embed_emit_step context label active saved tape, edge]
      rfl

def embed_emit_path (context : Store) (before after : EmitState)
    (path : EmitPath 29 context.marked before after) (afterLive : after.l ≠ none) :
    ActualPath (TM1.step program) (embedEmit context before) (embedEmit context after) where
  posts := path.posts.map (embedEmit context)
  chain := by
    change ((before :: path.posts).map (embedEmit context)).IsChain
      (fun x y => TM1.step program x = some y)
    apply (List.isChain_map _).mpr
    apply path.chain.imp_of_mem_imp
    intro old next _ nextMember edge
    exact embed_emit_edge context old next edge (emit_path_live _ _ _ path afterLive next nextMember)
  last := by
    change ((before :: path.posts).map (embedEmit context)).getLast? = some (embedEmit context after)
    rw [List.getLast?_map, path.last]
    rfl

/-- ONE selected physical 65-row emission inside the final bootloader.
The witness is the mapped actual old path and has exactly its length. -/
theorem program_emit_one_bit (context : Store) (bit : Bool) (gap : Nat)
    (rows : List (Bool × Bool)) (suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (⟨some 9, context, Tape.mk₂ (List.replicate gap false ++ true :: leftRows 29 rows)
        (true :: bit :: suffix)⟩ : TM1.Cfg Bool Label Store)
      (⟨some (PDROC.BitVM.Common.IO.Bootstrap.dispatch context.next), { context with bit := bit },
        Tape.mk₂ (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, context.marked)]))
          (true :: suffix)⟩ : TM1.Cfg Bool Label Store),
      path.posts.length ≤ 2 * gap + 2 * rows.length + 7 := by
  obtain ⟨path, bound⟩ := emit_one_bit_path 29 context.marked context.bit bit gap rows suffix
  let lifted := embed_emit_path context _ _ path (by simp [emitState])
  have first : embedEmit context
      (emitState (some 0) context.bit (List.replicate gap false ++ true :: leftRows 29 rows) (true :: bit :: suffix)) =
      (⟨some 9, context, Tape.mk₂ (List.replicate gap false ++ true :: leftRows 29 rows)
        (true :: bit :: suffix)⟩ : TM1.Cfg Bool Label Store) := by cases context; rfl
  have last : embedEmit context
      (emitState (some 5) bit
        (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, context.marked)])) (true :: suffix)) =
      (⟨some (PDROC.BitVM.Common.IO.Bootstrap.dispatch context.next), { context with bit := bit },
        Tape.mk₂ (List.replicate (gap + 1) false ++ true :: leftRows 29 (rows ++ [(bit, context.marked)]))
          (true :: suffix)⟩ : TM1.Cfg Bool Label Store) := rfl
  refine ⟨⟨lifted.posts, ?_, ?_⟩, ?_⟩
  · simpa only [first] using lifted.chain
  · simpa only [first, last] using lifted.last
  · simpa only [lifted, embed_emit_path, List.length_map] using bound

theorem program_return_cursor (context : Store) (gap : Nat) (rows : List (Bool × Bool))
    (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (⟨some 12, context, Tape.mk₂ left
        (physicalRows 29 rows ++ true :: (List.replicate gap false ++ true :: suffix))⟩ :
          TM1.Cfg Bool Label Store)
      (⟨some (PDROC.BitVM.Common.IO.Bootstrap.dispatch context.next), context,
        Tape.mk₂ (List.replicate gap false ++ true :: ((physicalRows 29 rows).reverse ++ left))
          (true :: suffix)⟩ : TM1.Cfg Bool Label Store),
      path.posts.length ≤ rows.length + gap + 2 := by
  obtain ⟨first, firstBound⟩ := return_rows_path 29 context.marked context.bit rows left
    (List.replicate gap false ++ true :: suffix)
  obtain ⟨second, secondBound⟩ := cursorSearch_path 29 context.marked context.bit gap
    (true :: ((physicalRows 29 rows).reverse ++ left)) suffix
  let old := first.trans second
  let lifted := embed_emit_path context _ _ old (by simp [emitState])
  have initial : embedEmit context (emitState (some 3) context.bit left
      (physicalRows 29 rows ++ true :: (List.replicate gap false ++ true :: suffix))) =
      (⟨some 12, context, Tape.mk₂ left
        (physicalRows 29 rows ++ true :: (List.replicate gap false ++ true :: suffix))⟩ :
          TM1.Cfg Bool Label Store) := by cases context; rfl
  have terminal : embedEmit context (emitState (some 5) context.bit
      (List.replicate gap false ++ true :: ((physicalRows 29 rows).reverse ++ left)) (true :: suffix)) =
      (⟨some (PDROC.BitVM.Common.IO.Bootstrap.dispatch context.next), context,
        Tape.mk₂ (List.replicate gap false ++ true :: ((physicalRows 29 rows).reverse ++ left))
          (true :: suffix)⟩ : TM1.Cfg Bool Label Store) := by cases context; rfl
  refine ⟨⟨lifted.posts, ?_, ?_⟩, ?_⟩
  · simpa only [initial] using lifted.chain
  · simpa only [initial, terminal] using lifted.last
  · have oldBound : old.posts.length ≤ rows.length + gap + 2 := by
      rw [ActualPath.trans_length]
      omega
    simpa only [lifted, embed_emit_path, List.length_map] using oldBound

end PDROC.BitVM.Common.IO.Wide
