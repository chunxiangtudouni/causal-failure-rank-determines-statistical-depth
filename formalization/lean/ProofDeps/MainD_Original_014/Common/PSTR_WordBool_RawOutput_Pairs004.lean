module

public import Common.PSTR_WordBool_RawOutput_ExtractCode003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Edge (before after : State) : Prop := TM1.step sourceMachine before = some after

theorem move_right_word (word left right : List Bool) :
    (Tape.move .right)^[word.length] (Tape.mk₂ left (word ++ right)) =
      Tape.mk₂ (word.reverse ++ left) right := by
  induction word generalizing left with
  | nil => rfl
  | cons bit later ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have first : (Tape.mk₂ left ((bit :: later) ++ right)).move .right =
        Tape.mk₂ (bit :: left) (later ++ right) := by simp [Tape.mk₂]
    rw [first, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem move_left_word (word left right : List Bool) :
    (Tape.move .left)^[word.length] (Tape.mk₂ (word ++ left) right) =
      Tape.mk₂ left (word.reverse ++ right) := by
  induction word generalizing right with
  | nil => rfl
  | cons bit later ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have first : (Tape.mk₂ ((bit :: later) ++ left) right).move .left =
        Tape.mk₂ (later ++ left) (bit :: right) := by simp [Tape.mk₂]
    rw [first, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem blocks_reverse (bits : List Bool) :
    (PSTRTMIncrement009.blocks bits).reverse = PSTRTMRawNat010.leftBlocks bits.reverse := by
  induction bits with
  | nil => rfl
  | cons bit later ih =>
    unfold PSTRTMIncrement009.blocks at ih
    simp only [PSTRTMIncrement009.blocks, List.flatMap_cons, List.cons_append,
      List.nil_append, List.reverse_cons]
    rw [ih]
    simp [PSTRTMRawNat010.leftBlocks, List.flatMap_append, List.append_assoc]

/-- West is in nearest-first order; east remains in physical output order. -/
def seekCfg (saved : Bool) (west east bank : List Bool) : State :=
  match west with
  | [] => cfg (seekOutput saved) [] (false :: (PSTRTMIncrement009.blocks east ++ [false,false] ++ bank))
  | bit :: later => cfg (seekOutput saved) (bit :: PSTRTMRawNat010.leftBlocks later)
      (true :: (PSTRTMIncrement009.blocks east ++ [false,false] ++ bank))

theorem seek_pair_step (saved bit : Bool) (later east bank : List Bool) :
    Edge (seekCfg saved (bit :: later) east bank) (seekCfg saved later (bit :: east) bank) := by
  cases later <;> cases saved <;>
    simp [Edge, seekCfg, cfg, sourceMachine, seekOutput, TM1.step, TM1.stepAux,
      readBit, mv, jump, Function.iterate_succ_apply, Tape.mk₂,
      PSTRTMRawNat010.leftBlocks, PSTRTMIncrement009.blocks]

theorem seek_pairs (saved : Bool) (west east bank : List Bool) :
    ∃ rest : List State, (seekCfg saved west east bank :: rest).IsChain Edge ∧
      (seekCfg saved west east bank :: rest).getLast? =
        some (seekCfg saved [] (west.reverse ++ east) bank) ∧ rest.length=west.length := by
  induction west generalizing east with
  | nil => exact ⟨[], .singleton _, rfl, rfl⟩
  | cons bit later ih =>
    obtain ⟨rest, chain, last, clock⟩ := ih (bit :: east)
    refine ⟨seekCfg saved later (bit :: east) bank :: rest,
      List.isChain_cons_cons.mpr ⟨seek_pair_step saved bit later east bank,chain⟩, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using last
    · simp only [List.length_cons,clock]

def returnCfg (previous remaining bank : List Bool) : State :=
  match remaining with
  | [] => cfg 7 (false :: PSTRTMRawNat010.leftBlocks previous) (false :: bank)
  | bit :: later => cfg 7 (bit :: PSTRTMRawNat010.leftBlocks previous)
      (true :: (PSTRTMIncrement009.blocks later ++ [false,false] ++ bank))

/-- The saved bit is really written into the new DATA cell and its flag is
really written TRUE. The next state is at an existing flag or the boundary. -/
theorem push_pair (saved : Bool) (existing bank : List Bool) :
    Edge (seekCfg saved [] existing bank) (returnCfg [saved] existing bank) := by
  cases existing <;> cases saved <;>
    simp [Edge, seekCfg, returnCfg, cfg, sourceMachine, seekOutput, TM1.step, TM1.stepAux,
      readBit, mv, jump, put, Function.iterate_succ_apply, Tape.mk₂,
      PSTRTMRawNat010.leftBlocks, PSTRTMIncrement009.blocks]

theorem return_pair_step (previous later bank : List Bool) (bit : Bool) :
    Edge (returnCfg previous (bit :: later) bank) (returnCfg (bit :: previous) later bank) := by
  cases later <;>
    simp [Edge, returnCfg, cfg, sourceMachine, TM1.step, TM1.stepAux,
      readBit, mv, jump, Function.iterate_succ_apply, Tape.mk₂,
      PSTRTMRawNat010.leftBlocks, PSTRTMIncrement009.blocks]

theorem return_pairs (previous remaining bank : List Bool) :
    ∃ rest : List State, (returnCfg previous remaining bank :: rest).IsChain Edge ∧
      (returnCfg previous remaining bank :: rest).getLast? =
        some (returnCfg (remaining.reverse ++ previous) [] bank) ∧
      rest.length=remaining.length := by
  induction remaining generalizing previous with
  | nil => exact ⟨[], .singleton _, rfl, rfl⟩
  | cons bit later ih =>
    obtain ⟨rest, chain, last, clock⟩ := ih (bit :: previous)
    refine ⟨returnCfg (bit :: previous) later bank :: rest,
      List.isChain_cons_cons.mpr ⟨return_pair_step previous later bank bit,chain⟩, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using last
    · simp only [List.length_cons,clock]

theorem return_boundary (bits body : List Bool) :
    Edge (returnCfg bits.reverse [] (guardRow ++ body))
      (cfg 1 (guardRow.reverse ++ workLeft bits) body) := by
  change some (TM1.stepAux (mv 34 .right (jump 1)) ()
    (Tape.mk₂ (false :: PSTRTMRawNat010.leftBlocks bits.reverse)
      ((false :: guardRow) ++ body))) = _
  rw [mv_step]
  rw [show 34=(false :: guardRow).length by rfl, move_right_word]
  simp [jump, TM1.stepAux, cfg, workLeft, blocks_reverse, List.reverse_cons, List.append_assoc]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
