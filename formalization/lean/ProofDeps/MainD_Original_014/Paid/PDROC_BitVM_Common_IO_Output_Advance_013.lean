module

public import Paid.PDROC_BitVM_Common_IO_Output_Shuttle_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

/-- Only existing trailing BLANKS are represented explicitly. This
equality does not clear any datum and performs no machine action. -/
theorem tape_two_blanks (left right : List Bool) :
    Tape.mk₂ left (right ++ [false, false]) = Tape.mk₂ left right := by
  have first := Wide.tape_right_blank left (right ++ [false])
  have second := Wide.tape_right_blank left right
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using first.trans second

theorem readyTape_unpadded (archive emitted : List Bool) :
    readyTape archive emitted = (fun old : Tape Bool => old.move .right)^[4]
      (Tape.mk₂ archive (true :: false :: false :: PSTRTMIncrement009.blocks emitted)) := by
  apply congrArg ((fun old : Tape Bool => old.move .right)^[4])
  simpa only [List.cons_append] using
    tape_two_blanks archive (true :: false :: false :: PSTRTMIncrement009.blocks emitted)

def sourceTail (bit : Bool) (other : OtherTail) : RowTail :=
  ⟨true :: bit :: other.toList, by simp⟩

theorem sourceTail_bits (bottom bit : Bool) (other : OtherTail) :
    rowBits bottom (sourceTail bit other) = presentRow bottom bit other := rfl

/-- Two actual source transitions: clear old cursor BEFORE LEFT65,
then read oldbottom/actualbit and mark the preceding source row, RIGHT65.
All prior output and all other stacks remain exactly in the whole tape. -/
theorem advance_mark_path (saved : Store) (notBottom : saved.bottom = false)
    (previousBottom previousBit : Bool) (previousOther : OtherTail)
    (below : List Bool) (cursor : RowTail) (above : List RowTail) (emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 7 saved (cursorTape ((presentRow previousBottom previousBit previousOther).reverse ++ below)
        cursor above emitted))
      (cfg 3 { saved with bottom := previousBottom, bit := previousBit }
        (Tape.mk₂ ((presentRow true previousBit previousOther).reverse ++ below)
          (flatRows (cursor :: above) ++ true :: false :: false :: PSTRTMIncrement009.blocks emitted))),
      path.posts.length = 2 := by
  let afterCursor := rowBits false cursor ++ flatRows above ++
    true :: false :: false :: PSTRTMIncrement009.blocks emitted
  have moved := Wide.moveCode_left (presentRow previousBottom previousBit previousOther).reverse below afterCursor saved
    (.goto (fun _ _ => 8) : Statement)
  have width : (presentRow previousBottom previousBit previousOther).reverse.length = 65 := by
    simp [presentRow_length]
  rw [width, Wide.moveCode_semantics] at moved
  simp only [List.reverse_reverse] at moved
  have tape := congrArg TM1.Cfg.Tape moved
  change (fun old : Tape Bool => old.move .left)^[65]
      (Tape.mk₂ ((presentRow previousBottom previousBit previousOther).reverse ++ below) afterCursor) =
    Tape.mk₂ below (presentRow previousBottom previousBit previousOther ++ afterCursor) at tape
  have edge := source_advance_step saved notBottom
    (cursorTape ((presentRow previousBottom previousBit previousOther).reverse ++ below) cursor above emitted)
  have cleared : (cursorTape ((presentRow previousBottom previousBit previousOther).reverse ++ below)
      cursor above emitted).write false =
      Tape.mk₂ ((presentRow previousBottom previousBit previousOther).reverse ++ below) afterCursor := by
    simp [cursorTape, afterCursor, rowBits, Tape.mk₂]
  rw [cleared, tape] at edge
  have marked := markCurrent_effect 3 saved previousBottom true previousBit below
    (previousOther.toList ++ afterCursor)
  have movedRight := Wide.moveCode_right (presentRow true previousBit previousOther) below afterCursor
    { saved with bottom := previousBottom, bit := previousBit } (.goto (fun _ _ => 3) : Statement)
  rw [presentRow_length, Wide.moveCode_semantics] at movedRight
  have rightTape := congrArg TM1.Cfg.Tape movedRight
  change (fun old : Tape Bool => old.move .right)^[65]
      (Tape.mk₂ below (presentRow true previousBit previousOther ++ afterCursor)) =
    Tape.mk₂ ((presentRow true previousBit previousOther).reverse ++ below) afterCursor at rightTape
  have next : TM1.step program
      (cfg 8 saved (Tape.mk₂ below (presentRow previousBottom previousBit previousOther ++ afterCursor))) =
      some (cfg 3 { saved with bottom := previousBottom, bit := previousBit }
        (Tape.mk₂ ((presentRow true previousBit previousOther).reverse ++ below) afterCursor)) := by
    change some (TM1.stepAux (markCurrent 3) saved
      (Tape.mk₂ below (presentRow previousBottom previousBit previousOther ++ afterCursor))) = _
    have effect : TM1.stepAux (markCurrent 3) saved
        (Tape.mk₂ below (presentRow previousBottom previousBit previousOther ++ afterCursor)) =
        cfg 3 { saved with bottom := previousBottom, bit := previousBit }
          ((fun old : Tape Bool => old.move .right)^[65]
            (Tape.mk₂ below (presentRow true previousBit previousOther ++ afterCursor))) := by
      simpa [presentRow] using marked
    rw [effect, rightTape]
  let joined := (ActualPath.single edge).trans (ActualPath.single next)
  refine ⟨⟨joined.posts, joined.chain, ?_⟩, rfl⟩
  simpa only [afterCursor, flatRows, List.flatMap_cons] using joined.last

/-- The preceding real source row is now ready at the output flag.
The changed data bit/bottom flag are actually read, not passed as an
answer or successful-run premise to the fixed finite machine. -/
theorem advance_ready_path (saved : Store) (notBottom : saved.bottom = false)
    (previousBottom previousBit : Bool) (previousOther : OtherTail)
    (below : List Bool) (cursor : RowTail) (above : List RowTail) (emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 7 saved (cursorTape ((presentRow previousBottom previousBit previousOther).reverse ++ below)
        cursor above emitted))
      (cfg 4 { saved with bottom := previousBottom, bit := previousBit }
        (readyTape (fullArchive below (sourceTail previousBit previousOther) (cursor :: above)) emitted)),
      path.posts.length = above.length + 4 := by
  obtain ⟨first, firstLength⟩ := advance_mark_path saved notBottom previousBottom previousBit previousOther
    below cursor above emitted
  obtain ⟨⟨posts, chain, last⟩, length⟩ := seek_anchor_path false
    { saved with bottom := previousBottom, bit := previousBit } (cursor :: above)
    ((presentRow true previousBit previousOther).reverse ++ below)
    (false :: false :: PSTRTMIncrement009.blocks emitted)
  have lengthBound : posts.length = above.length + 2 := by simpa using length
  let later : ActualPath (TM1.step program)
      (cfg 3 { saved with bottom := previousBottom, bit := previousBit }
        (Tape.mk₂ ((presentRow true previousBit previousOther).reverse ++ below)
          (flatRows (cursor :: above) ++ true :: false :: false :: PSTRTMIncrement009.blocks emitted)))
      (cfg 4 { saved with bottom := previousBottom, bit := previousBit }
        (readyTape (fullArchive below (sourceTail previousBit previousOther) (cursor :: above)) emitted)) :=
    ⟨posts, chain,
      by simpa [readyTape_unpadded, fullArchive, sourceTail_bits, seekLabel, seekTarget,
        seekOffset, List.append_assoc] using last⟩
  refine ⟨first.trans later, ?_⟩
  simp only [ActualPath.trans, later, List.length_append]
  omega

end PDROC.BitVM.Common.IO.Output
