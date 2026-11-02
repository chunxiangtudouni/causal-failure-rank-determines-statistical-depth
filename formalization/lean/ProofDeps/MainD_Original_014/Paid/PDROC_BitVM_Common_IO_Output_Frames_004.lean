module

public import Paid.PDROC_BitVM_Common_IO_Output_Probe_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

/-- A fixed64-cell physical row tail in the proof frame, NOT a machine
store or alphabet. Arbitrary other-track values remain actual tape data. -/
abbrev RowTail := List.Vector Bool 64

def rowBits (bottom : Bool) (tail : RowTail) : List Bool := bottom :: tail.toList

def flatRows (rows : List RowTail) : List Bool := rows.flatMap (rowBits false)

theorem rowBits_length (bottom : Bool) (tail : RowTail) : (rowBits bottom tail).length = 65 := by
  simp [rowBits]

def seekLabel (finish : Bool) : Label := if finish then 9 else 3

def seekTarget (finish : Bool) : Label := if finish then 10 else 4

def seekOffset (finish : Bool) : Nat := if finish then 3 else 4

theorem program_seek (finish : Bool) : program (seekLabel finish) =
    .branch (fun symbol _ => symbol)
      (Wide.moveCode .right (seekOffset finish) (.goto (fun _ _ => seekTarget finish)))
      (Wide.moveCode .right 65 (.goto (fun _ _ => seekLabel finish))) := by
  cases finish <;> rfl

/-- Read-only65-step travel over a row containing arbitrary readonly,
register or heap data. Only its genuine col0 controls the phase. -/
theorem seek_row_step (finish : Bool) (saved : Store) (tail : RowTail) (left suffix : List Bool) :
    TM1.step program (cfg (seekLabel finish) saved (Tape.mk₂ left (rowBits false tail ++ suffix))) =
      some (cfg (seekLabel finish) saved (Tape.mk₂ ((rowBits false tail).reverse ++ left) suffix)) := by
  have moved := Wide.moveCode_right (rowBits false tail) left suffix saved
    (.goto (fun _ _ => seekLabel finish) : Statement)
  rw [rowBits_length] at moved
  change some (TM1.stepAux (program (seekLabel finish)) saved (Tape.mk₂ left (rowBits false tail ++ suffix))) = _
  rw [program_seek]
  change some (TM1.stepAux (Wide.moveCode .right 65 (.goto (fun _ _ => seekLabel finish)))
    saved (Tape.mk₂ left (rowBits false tail ++ suffix))) = _
  rw [moved]
  rfl

theorem seek_anchor_step (finish : Bool) (saved : Store) (left suffix : List Bool) :
    TM1.step program (cfg (seekLabel finish) saved (Tape.mk₂ left (true :: suffix))) =
      some (cfg (seekTarget finish) saved
        ((fun old : Tape Bool => old.move .right)^[seekOffset finish] (Tape.mk₂ left (true :: suffix)))) := by
  change some (TM1.stepAux (program (seekLabel finish)) saved (Tape.mk₂ left (true :: suffix))) = _
  rw [program_seek]
  change some (TM1.stepAux
    (Wide.moveCode .right (seekOffset finish) (.goto (fun _ _ => seekTarget finish))) saved
    (Tape.mk₂ left (true :: suffix))) = _
  rw [Wide.moveCode_semantics]
  rfl

/-- The SAME actual path travels to the real right endAnchor. All old
row contents are preserved, with the actual head offset4 for appending or
offset3 for final inverse-codec entry. No decoded host list is executed. -/
theorem seek_anchor_path (finish : Bool) (saved : Store) (rows : List RowTail) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg (seekLabel finish) saved (Tape.mk₂ left (flatRows rows ++ true :: suffix)))
      (cfg (seekTarget finish) saved
        ((fun old : Tape Bool => old.move .right)^[seekOffset finish]
          (Tape.mk₂ ((flatRows rows).reverse ++ left) (true :: suffix)))),
      path.posts.length = rows.length + 1 := by
  induction rows generalizing left with
  | nil => exact ⟨ActualPath.single (seek_anchor_step finish saved left suffix), rfl⟩
  | cons tail rows ih =>
    have edge := seek_row_step finish saved tail left (flatRows rows ++ true :: suffix)
    obtain ⟨⟨posts, chain, last⟩, length⟩ := ih ((rowBits false tail).reverse ++ left)
    have lengthBound : posts.length = rows.length + 1 := length
    let later : ActualPath (TM1.step program)
        (cfg (seekLabel finish) saved
          (Tape.mk₂ ((rowBits false tail).reverse ++ left) (flatRows rows ++ true :: suffix)))
        (cfg (seekTarget finish) saved
          ((fun old : Tape Bool => old.move .right)^[seekOffset finish]
            (Tape.mk₂ ((flatRows (tail :: rows)).reverse ++ left) (true :: suffix)))) :=
      ⟨posts, chain, by simpa [flatRows, List.reverse_append, List.append_assoc] using last⟩
    let joined := (ActualPath.single edge).trans later
    refine ⟨⟨joined.posts, ?_, ?_⟩, ?_⟩
    · simpa [flatRows, List.append_assoc] using joined.chain
    · simpa [flatRows, List.append_assoc] using joined.last
    · simp only [joined, ActualPath.trans, ActualPath.single, later, List.length_append,
        List.length_cons, List.length_nil]
      omega

end PDROC.BitVM.Common.IO.Output
