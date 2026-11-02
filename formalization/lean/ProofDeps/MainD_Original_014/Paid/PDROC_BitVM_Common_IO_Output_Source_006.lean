module

public import Paid.PDROC_BitVM_Common_IO_Output_Frames_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

abbrev OtherTail := List.Vector Bool 62

def presentRow (bottom bit : Bool) (other : OtherTail) : List Bool :=
  bottom :: true :: bit :: other.toList

theorem presentRow_length (bottom bit : Bool) (other : OtherTail) :
    (presentRow bottom bit other).length = 65 := by simp [presentRow]

/-- Genuine presence0 observation, then65 physical moves. The two
initial RIGHT/LEFT moves are also part of the fixed statement and its
SupportClock bill; no row value or other stack cell is changed. -/
theorem top_skip_step (saved : Store) (bottom bit : Bool) (other : OtherTail) (left suffix : List Bool) :
    TM1.step program (cfg 0 saved (Tape.mk₂ left (presentRow bottom bit other ++ suffix))) =
      some (cfg 0 saved (Tape.mk₂ ((presentRow bottom bit other).reverse ++ left) suffix)) := by
  have moved := Wide.moveCode_right (presentRow bottom bit other) left suffix saved
    (.goto (fun _ _ => 0) : Statement)
  rw [presentRow_length] at moved
  change some (TM1.stepAux (Wide.moveCode .right 65 (.goto (fun _ _ => 0))) saved
    (Tape.mk₂ left (presentRow bottom bit other ++ suffix))) = _
  rw [moved]
  rfl

/-- First absent stack0 presence returns exactly one row to its real
top. For the original Artifact stream there is at least one present row,
proved from encodeBits, rather than supplied as a runtime length. -/
theorem top_stop_step (saved : Store) (bottom : Bool) (front left suffix : List Bool)
    (width : front.length = 65) :
    TM1.step program (cfg 0 saved (Tape.mk₂ (front ++ left) (bottom :: false :: suffix))) =
      some (cfg 1 saved (Tape.mk₂ left (front.reverse ++ bottom :: false :: suffix))) := by
  have moved := Wide.moveCode_left front left (bottom :: false :: suffix) saved
    (.goto (fun _ _ => 1) : Statement)
  rw [width] at moved
  change some (TM1.stepAux (Wide.moveCode .left 65 (.goto (fun _ _ => 1))) saved
    (Tape.mk₂ (front ++ left) (bottom :: false :: suffix))) = _
  rw [moved]
  rfl

abbrev PresentRow := Bool × Bool × OtherTail

def presentRows (rows : List PresentRow) : List Bool :=
  rows.flatMap (fun row => presentRow row.1 row.2.1 row.2.2)

/-- Actual read-only scan over all output-present rows. The proof list
specifies already existing physical cells and never enters finite sigma. -/
theorem top_skip_path (saved : Store) (rows : List PresentRow) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₂ left (presentRows rows ++ suffix)))
      (cfg 0 saved (Tape.mk₂ ((presentRows rows).reverse ++ left) suffix)),
      path.posts.length = rows.length := by
  induction rows generalizing left with
  | nil => exact ⟨ActualPath.refl _, rfl⟩
  | cons row rows ih =>
    rcases row with ⟨bottom, bit, other⟩
    have edge := top_skip_step saved bottom bit other left (presentRows rows ++ suffix)
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih ((presentRow bottom bit other).reverse ++ left)
    have lengthBound : posts.length = rows.length := length
    let later : ActualPath (TM1.step program)
        (cfg 0 saved (Tape.mk₂ ((presentRow bottom bit other).reverse ++ left) (presentRows rows ++ suffix)))
        (cfg 0 saved (Tape.mk₂ ((presentRows ((bottom, bit, other) :: rows)).reverse ++ left) suffix)) :=
      ⟨posts, chain, by simpa [presentRows, List.reverse_append, List.append_assoc] using last⟩
    let joined := (ActualPath.single edge).trans later
    refine ⟨⟨joined.posts, ?_, ?_⟩, ?_⟩
    · simpa [presentRows, List.append_assoc] using joined.chain
    · simpa [presentRows, List.append_assoc] using joined.last
    · simp only [joined, ActualPath.trans, ActualPath.single, later, List.length_append,
        List.length_cons, List.length_nil]
      omega

theorem source_back_step (saved : Store) (previous : Bool) (tail : RowTail) (left suffix : List Bool) :
    TM1.step program (cfg 6 saved (Tape.mk₂ ((rowBits previous tail).reverse ++ left) (false :: suffix))) =
      some (cfg 6 saved (Tape.mk₂ left (rowBits previous tail ++ false :: suffix))) := by
  have moved := Wide.moveCode_left (rowBits previous tail).reverse left (false :: suffix) saved
    (.goto (fun _ _ => 6) : Statement)
  have width : (rowBits previous tail).reverse.length = 65 := by simp [rowBits_length]
  rw [width] at moved
  change some (TM1.stepAux (Wide.moveCode .left 65 (.goto (fun _ _ => 6))) saved
    (Tape.mk₂ ((rowBits previous tail).reverse ++ left) (false :: suffix))) = _
  rw [moved]
  simp only [List.reverse_reverse]
  rfl

theorem source_found_step (saved : Store) (left suffix : List Bool) :
    TM1.step program (cfg 6 saved (Tape.mk₂ left (true :: suffix))) =
      some (cfg 7 saved (Tape.mk₂ left (true :: suffix))) := rfl

theorem source_finish_step (saved : Store) (bottom : saved.bottom = true) (tape : Tape Bool) :
    TM1.step program (cfg 7 saved tape) =
      some (cfg 9 saved ((fun old : Tape Bool => old.move .right)^[65] tape)) := by
  change some (TM1.stepAux (.branch (fun _ saved => saved.bottom)
    (Wide.moveCode .right 65 (.goto (fun _ _ => 9)))
    (.write (fun _ _ => false) (Wide.moveCode .left 65 (.goto (fun _ _ => 8))))) saved tape) = _
  simp only [TM1.stepAux, bottom, Wide.moveCode_semantics]
  rfl

/-- Old cursor is really cleared BEFORE the next row is read/marked.
No source presence/value is overwritten and no old bottom is cleared. -/
theorem source_advance_step (saved : Store) (bottom : saved.bottom = false) (tape : Tape Bool) :
    TM1.step program (cfg 7 saved tape) =
      some (cfg 8 saved ((fun old : Tape Bool => old.move .left)^[65] (tape.write false))) := by
  change some (TM1.stepAux (.branch (fun _ saved => saved.bottom)
    (Wide.moveCode .right 65 (.goto (fun _ _ => 9)))
    (.write (fun _ _ => false) (Wide.moveCode .left 65 (.goto (fun _ _ => 8))))) saved tape) = _
  simp only [TM1.stepAux, bottom, Wide.moveCode_semantics]
  rfl

end PDROC.BitVM.Common.IO.Output
