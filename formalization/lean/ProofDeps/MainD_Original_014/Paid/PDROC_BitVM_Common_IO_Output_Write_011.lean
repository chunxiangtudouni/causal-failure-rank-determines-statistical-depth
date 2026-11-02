module

public import Paid.PDROC_BitVM_Common_IO_Output_Setup_009
public import Paid.PDROC_BitVM_Common_IO_Output_Blocks_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def readyTape (archive emitted : List Bool) : Tape Bool :=
  (fun old : Tape Bool => old.move .right)^[4]
    (Tape.mk₂ archive (true :: false :: false :: (PSTRTMIncrement009.blocks emitted ++ [false, false])))

def appendSlot (archive emitted : List Bool) : Tape Bool :=
  Tape.mk₂ (false :: ((PSTRTMIncrement009.blocks emitted).reverse ++ false :: false :: true :: archive)) [false]

theorem readyTape_nil (archive : List Bool) : readyTape archive [] = appendSlot archive [] := by
  simp [readyTape, appendSlot, PSTRTMIncrement009.blocks, Function.iterate_succ_apply, Tape.mk₂]

theorem readyTape_cons (archive : List Bool) (bit : Bool) (emitted : List Bool) :
    readyTape archive (bit :: emitted) =
      Tape.mk₂ (bit :: false :: false :: true :: archive)
        (true :: (PSTRTMIncrement009.blocks emitted ++ [false, false])) := by
  simp [readyTape, PSTRTMIncrement009.blocks, Function.iterate_succ_apply, Tape.mk₂]

theorem nextFlags_tail (values : List Bool) :
    nextFlags (values ++ [false]) = true :: (PSTRTMIncrement009.blocks values ++ [false]) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simpa [nextFlags, PSTRTMIncrement009.blocks, List.append_assoc] using
      congrArg (fun cells => true :: value :: cells) ih

/-- The genuine first-flag scan reaches the actually blank append slot.
All prior output data and the complete oldGamma archive remain. -/
theorem to_append_slot_path (saved : Store) (archive emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 4 saved (readyTape archive emitted)) (cfg 4 saved (appendSlot archive emitted)),
      path.posts.length = emitted.length := by
  cases emitted with
  | nil =>
    rw [readyTape_nil]
    exact ⟨ActualPath.refl _, rfl⟩
  | cons bit emitted =>
    obtain ⟨⟨posts, chain, last⟩, length⟩ := flag_right_path saved (emitted ++ [false])
      (bit :: false :: false :: true :: archive) []
    refine ⟨⟨posts, ?_, ?_⟩, ?_⟩
    · simpa [readyTape_cons, nextFlags_tail, List.append_assoc] using chain
    · simpa [readyTape_cons, appendSlot, nextFlags_tail, PSTRTMIncrement009.blocks,
        List.reverse_append, List.append_assoc] using last
    · simpa using length

theorem true_backData_cons (value : Bool) (values : List Bool) :
    true :: backData (value :: values) =
      (PSTRTMIncrement009.blocks (value :: values).reverse).reverse ++ [false] := by
  induction values generalizing value with
  | nil => rfl
  | cons previous values ih =>
    simpa [backData, PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append,
      List.reverse_append, List.append_assoc] using
      congrArg (fun cells => true :: value :: cells) (ih previous)

theorem backData_emitted (emitted : List Bool) (value : Bool) :
    backData (emitted ++ [value]).reverse = value :: ((PSTRTMIncrement009.blocks emitted).reverse ++ [false]) := by
  simpa [PSTRTMIncrement009.blocks, List.reverse_cons, List.reverse_append, List.flatMap_append,
    List.append_assoc] using true_backData_cons value emitted.reverse

/-- Write the actually read source bit, then genuinely scan every flag
back to the false guard. SAME selected source path and all oldGamma data;
no clear, decoded word, width, or successful-run oracle is an input. -/
theorem write_guard_path (saved : Store) (archive emitted : List Bool) :
    ∃ path : ActualPath (TM1.step program)
      (cfg 4 saved (readyTape archive emitted))
      (cfg 5 saved (Tape.mk₂ (false :: true :: archive)
        (false :: PSTRTMIncrement009.blocks (emitted ++ [saved.bit])))),
      path.posts.length = 2 * emitted.length + 2 := by
  obtain ⟨first, firstLength⟩ := to_append_slot_path saved archive emitted
  have edge := flag_append_step saved false
    ((PSTRTMIncrement009.blocks emitted).reverse ++ false :: false :: true :: archive) []
  obtain ⟨⟨posts, chain, last⟩, length⟩ :=
    back_flag_path saved (emitted ++ [saved.bit]).reverse (false :: true :: archive) []
  have lengthBound : posts.length = emitted.length + 1 := by simpa using length
  have framed : backData (saved.bit :: emitted.reverse) =
      saved.bit :: ((PSTRTMIncrement009.blocks emitted).reverse ++ [false]) := by
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using
      backData_emitted emitted saved.bit
  let later : ActualPath (TM1.step program)
      (cfg 5 saved (Tape.mk₂
        (saved.bit :: ((PSTRTMIncrement009.blocks emitted).reverse ++ false :: false :: true :: archive)) [true]))
      (cfg 5 saved (Tape.mk₂ (false :: true :: archive)
        (false :: PSTRTMIncrement009.blocks (emitted ++ [saved.bit])))) :=
    ⟨posts,
      by simpa [backFrame, framed, List.reverse_append, List.append_assoc] using chain,
      by simpa [backFrame, framed, List.reverse_append, List.append_assoc] using last⟩
  let appended : ActualPath (TM1.step program)
      (cfg 4 saved (appendSlot archive emitted))
      (cfg 5 saved (Tape.mk₂
        (saved.bit :: ((PSTRTMIncrement009.blocks emitted).reverse ++ false :: false :: true :: archive)) [true])) :=
    ActualPath.single edge
  let joined := (first.trans appended).trans later
  refine ⟨joined, ?_⟩
  simp only [joined, ActualPath.trans, appended, ActualPath.single, later, List.length_append,
    List.length_cons, List.length_nil]
  omega

end PDROC.BitVM.Common.IO.Output
