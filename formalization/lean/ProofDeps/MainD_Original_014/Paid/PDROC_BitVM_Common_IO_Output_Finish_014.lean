module

public import Paid.PDROC_BitVM_Common_IO_Output_Advance_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def blockTape (archive emitted : List Bool) : Tape Bool :=
  Tape.mk₂ (false :: false :: true :: archive) (PSTRTMIncrement009.blocks emitted ++ [false, false])

theorem finish_pointer (archive emitted : List Bool) :
    (fun old : Tape Bool => old.move .right)^[3]
      (Tape.mk₂ archive (true :: false :: false :: PSTRTMIncrement009.blocks emitted)) =
      blockTape archive emitted := by
  have shape : (fun old : Tape Bool => old.move .right)^[3]
      (Tape.mk₂ archive (true :: false :: false :: PSTRTMIncrement009.blocks emitted)) =
      Tape.mk₂ (false :: false :: true :: archive) (PSTRTMIncrement009.blocks emitted) := by
    simp [Function.iterate_succ_apply, Tape.mk₂]
  rw [shape]
  exact (tape_two_blanks _ _).symm

theorem native_entry (saved : Store) (tape : Tape Bool) :
    TM1.step program (cfg 10 saved tape) = some (cfg 11 saved tape) := rfl

/-- The REAL bottom flag ends extraction. The program really moves
across all remaining oldGamma rows to endAnchor, enters the actual old
inverse codec, scans away its header, and HALTs on the naked byte stream.
The entire old archive is retained; no free cleanup or host decode. -/
theorem finish_decode_path (saved : Store) (bottom : saved.bottom = true)
    (below : List Bool) (cursor : RowTail) (above : List RowTail) (emitted : List Bool) :
    ∃ final : TM1.Cfg Bool Label Store, ∃ path : ActualPath (TM1.step program)
      (cfg 7 saved (cursorTape below cursor above emitted)) final,
      final.l = none ∧ final.var = saved ∧ final.Tape.right₀ = ListBlank.mk emitted ∧
      path.posts.length ≤ above.length + 3 + 64 * (emitted.length + 1)^2 := by
  let tail := flatRows above ++ true :: false :: false :: PSTRTMIncrement009.blocks emitted
  have moved := Wide.moveCode_right (rowBits true cursor) below tail saved
    (.goto (fun _ _ => 9) : Statement)
  rw [rowBits_length, Wide.moveCode_semantics] at moved
  have tape := congrArg TM1.Cfg.Tape moved
  change (fun old : Tape Bool => old.move .right)^[65]
      (Tape.mk₂ below (rowBits true cursor ++ tail)) =
    Tape.mk₂ ((rowBits true cursor).reverse ++ below) tail at tape
  have before : cursorTape below cursor above emitted = Tape.mk₂ below (rowBits true cursor ++ tail) := by
    simp [cursorTape, tail, List.append_assoc]
  have edge := source_finish_step saved bottom (cursorTape below cursor above emitted)
  rw [before, tape] at edge
  obtain ⟨⟨posts, chain, last⟩, length⟩ := seek_anchor_path true saved above
    ((rowBits true cursor).reverse ++ below) (false :: false :: PSTRTMIncrement009.blocks emitted)
  have seekLength : posts.length = above.length + 1 := length
  let sought : ActualPath (TM1.step program)
      (cfg 9 saved (Tape.mk₂ ((rowBits true cursor).reverse ++ below) tail))
      (cfg 10 saved (blockTape (fullArchive below cursor above) emitted)) :=
    ⟨posts, chain,
      by simpa [fullArchive, seekLabel, seekTarget, seekOffset, finish_pointer, List.append_assoc] using last⟩
  obtain ⟨final, decoded, halted, store, right, decodedBound⟩ :=
    decode_blocks_bare_right saved (false :: true :: fullArchive below cursor above) emitted
  let decodedPath : ActualPath (TM1.step program)
      (cfg 11 saved (blockTape (fullArchive below cursor above) emitted)) final := decoded
  let joined := (((ActualPath.single edge).trans sought).trans
    (ActualPath.single (native_entry saved _))).trans decodedPath
  refine ⟨final, ⟨joined.posts, ?_, ?_⟩, halted, store, right, ?_⟩
  · simpa only [before] using joined.chain
  · simpa only [before] using joined.last
  · simp only [joined, ActualPath.trans, ActualPath.single, sought, decodedPath, List.length_append,
      List.length_cons, List.length_nil]
    omega

end PDROC.BitVM.Common.IO.Output
