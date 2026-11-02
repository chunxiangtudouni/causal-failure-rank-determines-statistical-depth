module

public import Paid.PDROC_BitVM_Common_IO_Output_End_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

/-- Proof frame for an ALREADY EXISTING nonempty oldGamma row.
This structure is never an alphabet, finite Store, instruction or input. -/
structure OccupiedRow where
  pairs : List (Bool × Bool)
  width : pairs.length = 32
  occupied : pairFound pairs = true

def occupiedBits (row : OccupiedRow) : List Bool := false :: pairBits row.pairs

def occupiedRows (rows : List OccupiedRow) : List Bool := rows.flatMap occupiedBits

theorem occupiedBits_length (row : OccupiedRow) : (occupiedBits row).length = 65 := by
  simp [occupiedBits, pairBits_length, row.width]

def blankPairs : List (Bool × Bool) := trackPairs (default : Wide.VMTrack)

/-- Actual all-stack end search, including the genuine blank-row probe,
rewind/anchor write and move to the first output flag. SAME source bit,
bottom flag and entire readonly/register/heap archive are retained. -/
theorem end_rows_path (saved : Store) (rows : List OccupiedRow) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 2 saved (Tape.mk₂ left
        (occupiedRows rows ++ false :: (pairBits blankPairs ++ suffix))))
      (cfg 4 (scannedStore saved false)
        ((fun old : Tape Bool => old.move .right)^[4]
          (Tape.mk₂ ((occupiedRows rows).reverse ++ left) (true :: (pairBits blankPairs ++ suffix))))),
      path.posts.length = rows.length + 1 := by
  induction rows generalizing saved left with
  | nil =>
    exact ⟨ActualPath.single (findEnd_empty saved blankPairs
      (trackPairs_length _) trackPairs_blank left suffix), rfl⟩
  | cons row rows ih =>
    have edge := findEnd_occupied saved row.pairs row.width row.occupied left
      (occupiedRows rows ++ false :: (pairBits blankPairs ++ suffix))
    obtain ⟨⟨posts, chain, last⟩, length⟩ :=
      ih (scannedStore saved true) ((occupiedBits row).reverse ++ left)
    have lengthBound : posts.length = rows.length + 1 := length
    let later : ActualPath (TM1.step program)
        (cfg 2 (scannedStore saved true) (Tape.mk₂ ((occupiedBits row).reverse ++ left)
          (occupiedRows rows ++ false :: (pairBits blankPairs ++ suffix))))
        (cfg 4 (scannedStore saved false)
          ((fun old : Tape Bool => old.move .right)^[4]
            (Tape.mk₂ ((occupiedRows (row :: rows)).reverse ++ left) (true :: (pairBits blankPairs ++ suffix))))) :=
      ⟨posts, chain, by
        simpa [occupiedRows, List.reverse_append, List.append_assoc, scannedStore] using last⟩
    let joined := (ActualPath.single edge).trans later
    refine ⟨⟨joined.posts, ?_, ?_⟩, ?_⟩
    · simpa [occupiedRows, occupiedBits, List.append_assoc] using joined.chain
    · simpa [occupiedRows, occupiedBits, List.append_assoc] using joined.last
    · simp only [joined, ActualPath.trans, ActualPath.single, later, List.length_append,
        List.length_cons, List.length_nil]
      omega

theorem mark_top_step (saved : Store) (bottom bit : Bool) (other : OtherTail) (left suffix : List Bool) :
    TM1.step program (cfg 1 saved (Tape.mk₂ left (presentRow bottom bit other ++ suffix))) =
      some (cfg 2 { saved with bottom := bottom, bit := bit }
        (Tape.mk₂ ((presentRow true bit other).reverse ++ left) suffix)) := by
  have marked := markCurrent_effect 2 saved bottom true bit left (other.toList ++ suffix)
  have moved := Wide.moveCode_right (presentRow true bit other) left suffix
    { saved with bottom := bottom, bit := bit } (.goto (fun _ _ => 2) : Statement)
  rw [presentRow_length, Wide.moveCode_semantics] at moved
  have tape := congrArg TM1.Cfg.Tape moved
  change (fun old : Tape Bool => old.move .right)^[65]
      (Tape.mk₂ left (presentRow true bit other ++ suffix)) =
    Tape.mk₂ ((presentRow true bit other).reverse ++ left) suffix at tape
  change some (TM1.stepAux (markCurrent 2) saved
    (Tape.mk₂ left (presentRow bottom bit other ++ suffix))) = _
  have mapped : TM1.stepAux (markCurrent 2) saved (Tape.mk₂ left (presentRow bottom bit other ++ suffix)) =
      cfg 2 { saved with bottom := bottom, bit := bit }
        ((fun old : Tape Bool => old.move .right)^[65]
          (Tape.mk₂ left (presentRow true bit other ++ suffix))) := by
    simpa [presentRow] using marked
  rw [mapped, tape]

/-- Initial output-top installation: all present rows are actually
scanned, the first absent row is observed, then the real top is returned
to and read/marked. No precomputed length or encoded tape is supplied. -/
theorem install_top_path (saved : Store) (rows : List PresentRow)
    (bottom bit : Bool) (other : OtherTail) (left suffix : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₂ left
        (presentRows (rows ++ [(bottom, bit, other)]) ++ false :: false :: suffix)))
      (cfg 2 { saved with bottom := bottom, bit := bit }
        (Tape.mk₂ ((presentRow true bit other).reverse ++ (presentRows rows).reverse ++ left)
          (false :: false :: suffix))),
      path.posts.length = rows.length + 3 := by
  obtain ⟨⟨posts, chain, last⟩, length⟩ := top_skip_path saved (rows ++ [(bottom, bit, other)]) left (false :: false :: suffix)
  have lengthBound : posts.length = rows.length + 1 := by simpa using length
  let topLeft := (presentRows rows).reverse ++ left
  let first : ActualPath (TM1.step program)
      (cfg 0 saved (Tape.mk₂ left (presentRows (rows ++ [(bottom, bit, other)]) ++ false :: false :: suffix)))
      (cfg 0 saved (Tape.mk₂ ((presentRow bottom bit other).reverse ++ topLeft) (false :: false :: suffix))) :=
    ⟨posts, chain, by
      simpa [topLeft, presentRows, List.flatMap_append, List.reverse_append, List.append_assoc] using last⟩
  have stop := top_stop_step saved false (presentRow bottom bit other).reverse topLeft suffix
    (by simp [presentRow_length])
  have returned : TM1.step program
      (cfg 0 saved (Tape.mk₂ ((presentRow bottom bit other).reverse ++ topLeft) (false :: false :: suffix))) =
      some (cfg 1 saved (Tape.mk₂ topLeft (presentRow bottom bit other ++ false :: false :: suffix))) := by
    simpa only [List.reverse_reverse] using stop
  have marked := mark_top_step saved bottom bit other topLeft (false :: false :: suffix)
  let joined := (first.trans (ActualPath.single returned)).trans (ActualPath.single marked)
  refine ⟨⟨joined.posts, joined.chain, ?_⟩, ?_⟩
  · simpa only [topLeft, List.append_assoc] using joined.last
  · simp only [joined, ActualPath.trans, ActualPath.single, first, List.length_append,
      List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Common.IO.Output
