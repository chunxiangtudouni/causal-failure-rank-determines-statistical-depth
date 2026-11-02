module

public import Paid.PDROC_BitVM_Common_IO_Wide_Counter_007
public import Paid.PDROC_BitVM_Common_IO_Wide_Codec_003

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

def dirtyRow (bottom bit marked : Bool) : List Bool :=
  [bottom, true, bit, marked] ++ List.replicate 59 false ++ [true, true]

/-- All 62 auxiliary cells, including absent-stack value bits, really
become FALSE. Merely clearing presence flags would not give this equality. -/
theorem clearAuxiliary65_effect (bottom bit marked : Bool) (saved : Store) (left right : List Bool)
    (next : Statement) :
    TM1.stepAux (clearAuxiliary65 next) saved (Tape.mk₂ left (dirtyRow bottom bit marked ++ right)) =
      TM1.stepAux next saved (Tape.mk₂ ((cleanRow 29 bottom bit).reverse ++ left) right) := by
  let first := [bottom, true, bit]
  let auxiliary := marked :: (List.replicate 59 false ++ [true, true])
  have length : auxiliary.length = 62 := by simp [auxiliary]
  have front := moveCode_right first left (auxiliary ++ right) saved (clearCode 62 next)
  have cleared := clearCode_overwrite auxiliary (first.reverse ++ left) right saved next
  rw [length] at cleared
  calc
    TM1.stepAux (clearAuxiliary65 next) saved (Tape.mk₂ left (dirtyRow bottom bit marked ++ right)) =
        TM1.stepAux (clearCode 62 next) saved (Tape.mk₂ (first.reverse ++ left) (auxiliary ++ right)) := by
          simpa [clearAuxiliary65, first, auxiliary, dirtyRow, List.append_assoc] using front
    _ = TM1.stepAux next saved (Tape.mk₂ ((cleanRow 29 bottom bit).reverse ++ left) right) := by
      simpa [cleanRow, padding, first, List.reverse_append, List.append_assoc] using cleared

theorem cleanup_first_row (saved : Store) (bit marked : Bool) (left right : List Bool) :
    TM1.step program (state 17 saved left (temporaryRow 29 bit marked ++ right)) =
      some (state 18 saved ((cleanRow 29 true bit).reverse ++ left) right) := by
  change some (TM1.stepAux (clearAuxiliary65 (.goto (fun _ _ => 18))) saved
    (Tape.mk₂ left (dirtyRow true bit marked ++ right))) = _
  rw [clearAuxiliary65_effect]
  rfl

theorem cleanup_later_row (saved : Store) (bit marked : Bool) (left right : List Bool) :
    TM1.step program (state 18 saved left (temporaryRow 29 bit marked ++ right)) =
      some (state 18 saved ((cleanRow 29 false bit).reverse ++ left) right) := by
  change some (TM1.stepAux (clearAuxiliary65 (.goto (fun _ _ => 18))) saved
    (Tape.mk₂ left (dirtyRow false bit marked ++ right))) = _
  rw [clearAuxiliary65_effect]
  rfl

/-- Anchor erasure and the first backward stride are real instructions. -/
theorem cleanup_erase_anchor (saved : Store) (bottom bit : Bool) (left right : List Bool) :
    TM1.step program (state 18 saved ((cleanRow 29 bottom bit).reverse ++ left) (true :: right)) =
      some (state 19 saved left (cleanRow 29 bottom bit ++ false :: right)) := by
  have moved := moveCode_left (cleanRow 29 bottom bit).reverse left (false :: right) saved
    (TM1.Stmt.goto (fun _ _ => (19 : Label)))
  have length : (cleanRow 29 bottom bit).reverse.length = 65 := by
    simpa only [List.length_reverse, stride] using cleanRow_length 29 bottom bit
  rw [length] at moved
  change some (TM1.stepAux (moveCode .left 65 (.goto (fun _ _ => 19))) saved
    (Tape.mk₂ ((cleanRow 29 bottom bit).reverse ++ left) (false :: right))) = _
  simpa only [TM1.stepAux, List.reverse_reverse, state] using congrArg some moved

theorem cleanup_back_row (saved : Store) (bottom bit : Bool) (left right : List Bool) :
    TM1.step program (state 19 saved ((cleanRow 29 bottom bit).reverse ++ left) (false :: right)) =
      some (state 19 saved left (cleanRow 29 bottom bit ++ false :: right)) := by
  have moved := moveCode_left (cleanRow 29 bottom bit).reverse left (false :: right) saved
    (TM1.Stmt.goto (fun _ _ => (19 : Label)))
  have length : (cleanRow 29 bottom bit).reverse.length = 65 := by
    simpa only [List.length_reverse, stride] using cleanRow_length 29 bottom bit
  rw [length] at moved
  change some (TM1.stepAux (moveCode .left 65 (.goto (fun _ _ => 19))) saved
    (Tape.mk₂ ((cleanRow 29 bottom bit).reverse ++ left) (false :: right))) = _
  simpa only [TM1.stepAux, List.reverse_reverse, state] using congrArg some moved

theorem cleanup_at_bottom (saved : Store) (left right : List Bool) :
    TM1.step program (state 19 saved left (true :: right)) =
      some (⟨none, saved, Tape.mk₂ left (true :: right)⟩ : TM1.Cfg Bool Label Store) := by
  simp [TM1.step, TM1.stepAux, program, state, Tape.mk₂]

def cleanRows (rows : List (Bool × Bool)) : List Bool := rows.flatMap (fun row => cleanRow 29 false row.1)

/-- Forward cleanup preserves every raw bit in the same selected actual
path. It clears all auxiliary columns of every remaining physical row. -/
theorem cleanup_rows_path (saved : Store) (rows : List (Bool × Bool)) (left right : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (state 18 saved left (physicalRows 29 rows ++ right))
      (state 18 saved ((cleanRows rows).reverse ++ left) right),
      path.posts.length ≤ rows.length := by
  induction rows generalizing left with
  | nil => exact ⟨ActualPath.refl _, Nat.le_refl _⟩
  | cons row rows ih =>
    obtain ⟨bit, marked⟩ := row
    obtain ⟨⟨posts, chain, last⟩, bound⟩ := ih ((cleanRow 29 false bit).reverse ++ left)
    have lengthBound : posts.length ≤ rows.length := bound
    let later : ActualPath (TM1.step program)
        (state 18 saved ((cleanRow 29 false bit).reverse ++ left) (physicalRows 29 rows ++ right))
        (state 18 saved ((cleanRows ((bit, marked) :: rows)).reverse ++ left) right) :=
      ⟨posts, chain, by simpa [cleanRows, List.reverse_append, List.append_assoc] using last⟩
    have edge : TM1.step program (state 18 saved left (physicalRows 29 ((bit, marked) :: rows) ++ right)) =
        some (state 18 saved ((cleanRow 29 false bit).reverse ++ left) (physicalRows 29 rows ++ right)) := by
      simpa only [physicalRows_cons, List.append_assoc] using
        cleanup_later_row saved bit marked left (physicalRows 29 rows ++ right)
    refine ⟨(ActualPath.single edge).trans later, ?_⟩
    simp only [ActualPath.trans_length, ActualPath.single, later, List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Common.IO.Wide
