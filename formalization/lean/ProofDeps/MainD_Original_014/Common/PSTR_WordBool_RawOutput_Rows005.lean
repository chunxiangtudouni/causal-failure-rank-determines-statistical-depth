module

public import Common.PSTR_WordBool_RawOutput_Pairs004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem doneRows_succ (count : Nat) : doneRows (count+1)=doneRow ++ doneRows count := by
  simp [doneRows, List.replicate_succ]

theorem doneRows_end (count : Nat) : doneRows (count+1)=doneRows count ++ doneRow := by
  induction count with
  | zero => simp [doneRows]
  | succ count ih =>
    calc
      doneRows (count+1+1)=doneRow ++ doneRows (count+1) := doneRows_succ (count+1)
      _=doneRow ++ (doneRows count ++ doneRow) := congrArg (fun cells => doneRow ++ cells) ih
      _=doneRows (count+1) ++ doneRow := by rw [doneRows_succ count,List.append_assoc]

theorem scan_row_step (left right : List Bool) :
    Edge (cfg 1 left (doneRow ++ right)) (cfg 1 (doneRow.reverse ++ left) right) := by
  change some (TM1.stepAux (mv 33 .right (jump 1)) () (Tape.mk₂ left (doneRow ++ right))) = _
  rw [mv_step, show 33=doneRow.length by rfl, move_right_word]
  rfl

theorem scan_rows (count : Nat) (left right : List Bool) :
    ∃ rest : List State, (cfg 1 left (doneRows count ++ right) :: rest).IsChain Edge ∧
      (cfg 1 left (doneRows count ++ right) :: rest).getLast? =
        some (cfg 1 ((doneRows count).reverse ++ left) right) ∧ rest.length=count := by
  induction count generalizing left with
  | zero => exact ⟨[], .singleton _, rfl, rfl⟩
  | succ count ih =>
    obtain ⟨rest, chain, last, clock⟩ := ih (doneRow.reverse ++ left)
    refine ⟨cfg 1 (doneRow.reverse ++ left) (doneRows count ++ right) :: rest, ?_, ?_, ?_⟩
    · apply List.isChain_cons_cons.mpr
      exact ⟨by simpa only [doneRows_succ,List.append_assoc] using
        scan_row_step left (doneRows count ++ right), chain⟩
    · simpa [doneRows_succ,List.reverse_append,List.append_assoc] using last
    · simp only [List.length_cons,clock]

theorem source_present (left right : List Bool) (bit : Bool) :
    Edge (cfg 1 left (dataRow bit ++ right))
      (cfg 2 (false :: left) (true :: bit :: (List.replicate 30 false ++ right))) := by
  simp [Edge,cfg,sourceMachine,TM1.step,TM1.stepAux,readBit,mv,jump,
    Function.iterate_succ_apply,dataRow,Tape.mk₂]

theorem read_present (left right : List Bool) (bit : Bool) :
    Edge (cfg 2 (false :: left) (true :: bit :: (List.replicate 30 false ++ right)))
      (cfg (shuttle bit) ([false,false,true] ++ left) (List.replicate 30 false ++ right)) := by
  cases bit <;>
    simp [Edge,cfg,sourceMachine,TM1.step,TM1.stepAux,readBit,mv,jump,put,
      shuttle,Tape.mk₂]

def shuttleCfg (saved : Bool) (older : Nat) (work right : List Bool) : State :=
  cfg (shuttle saved) ([false,false,true] ++ (doneRows older).reverse ++ guardRow.reverse ++ work)
    (List.replicate 30 false ++ right)

def guardCfg (saved : Bool) (work body : List Bool) : State :=
  cfg (shuttle saved) ([false,false,false] ++ work) (true :: (List.replicate 29 false ++ body))

private theorem done_reverse : doneRow.reverse=List.replicate 30 false ++ [false,false,true] := rfl
private theorem guard_reverse : guardRow.reverse=List.replicate 29 false ++ [true,false,false,false] := rfl
private theorem done_shape : doneRow=[true,false,false] ++ List.replicate 30 false := rfl

theorem shuttle_move_succ (saved : Bool) (older : Nat) (work right : List Bool) :
    (Tape.move .left)^[33] (shuttleCfg saved (older+1) work right).Tape =
      (shuttleCfg saved older work (doneRow ++ right)).Tape := by
  let word : List Bool := [false,false,true] ++ List.replicate 30 false
  let tail := [false,false,true] ++ (doneRows older).reverse ++ guardRow.reverse ++ work
  have leftEq : [false,false,true] ++ (doneRows (older+1)).reverse ++ guardRow.reverse ++ work = word ++ tail := by
    simp [word,tail,doneRows_end,List.reverse_append,done_reverse,List.append_assoc]
  change (Tape.move .left)^[33] (Tape.mk₂
    ([false,false,true] ++ (doneRows (older+1)).reverse ++ guardRow.reverse ++ work)
    (List.replicate 30 false ++ right)) = _
  rw [leftEq,show 33=word.length by rfl,move_left_word]
  have rev : word.reverse=List.replicate 30 false ++ [true,false,false] := rfl
  simp [shuttleCfg,cfg,tail,rev,done_shape,List.append_assoc]

theorem shuttle_move_zero (saved : Bool) (work right : List Bool) :
    (Tape.move .left)^[33] (shuttleCfg saved 0 work right).Tape =
      (guardCfg saved work (doneRow ++ right)).Tape := by
  let word : List Bool := [false,false,true] ++ List.replicate 29 false ++ [true]
  have leftEq : [false,false,true] ++ guardRow.reverse ++ work = word ++ ([false,false,false] ++ work) := by
    simp [word,guard_reverse,List.append_assoc]
  change (Tape.move .left)^[33] (Tape.mk₂ ([false,false,true] ++ guardRow.reverse ++ work)
    (List.replicate 30 false ++ right)) = _
  rw [leftEq,show 33=word.length by rfl,move_left_word]
  have rev : word.reverse=true :: (List.replicate 29 false ++ [true,false,false]) := rfl
  simp [guardCfg,cfg,rev,done_shape]

private theorem shuttle_false (saved : Bool) (left right : List Bool) :
    TM1.step sourceMachine (cfg (shuttle saved) left (List.replicate 30 false ++ right)) =
      some ⟨some (shuttle saved), (),
        (Tape.move .left)^[33] (Tape.mk₂ left (List.replicate 30 false ++ right))⟩ := by
  cases saved <;>
    simp [cfg,sourceMachine,shuttle,TM1.step,TM1.stepAux,readBit,mv_step,jump,Tape.mk₂]

theorem shuttle_step_succ (saved : Bool) (older : Nat) (work right : List Bool) :
    Edge (shuttleCfg saved (older+1) work right) (shuttleCfg saved older work (doneRow ++ right)) := by
  unfold Edge
  have tape := shuttle_move_succ saved older work right
  dsimp only [shuttleCfg,cfg] at tape
  rw [shuttleCfg,shuttle_false,tape]
  rfl

theorem shuttle_step_zero (saved : Bool) (work right : List Bool) :
    Edge (shuttleCfg saved 0 work right) (guardCfg saved work (doneRow ++ right)) := by
  unfold Edge
  have tape := shuttle_move_zero saved work right
  dsimp only [shuttleCfg,guardCfg,cfg] at tape
  rw [shuttleCfg,shuttle_false,tape]
  rfl

theorem shuttle_rows (saved : Bool) (older : Nat) (work right : List Bool) :
    ∃ rest : List State, (shuttleCfg saved older work right :: rest).IsChain Edge ∧
      (shuttleCfg saved older work right :: rest).getLast? =
        some (guardCfg saved work (doneRows (older+1) ++ right)) ∧ rest.length=older+1 := by
  induction older generalizing right with
  | zero =>
    refine ⟨[guardCfg saved work (doneRow ++ right)], ?_, ?_, rfl⟩
    · exact List.isChain_cons_cons.mpr ⟨shuttle_step_zero saved work right,.singleton _⟩
    · simp [doneRows]
  | succ older ih =>
    obtain ⟨rest,chain,last,clock⟩ := ih (doneRow ++ right)
    refine ⟨shuttleCfg saved older work (doneRow ++ right) :: rest,
      List.isChain_cons_cons.mpr ⟨shuttle_step_succ saved older work right,chain⟩, ?_, ?_⟩
    · simpa [doneRows_end,List.append_assoc] using last
    · simp only [List.length_cons,clock]

/-- The only TRUE read in the spare column is the real owned west guard.
Both the flag search and the saved-bit push stay west of that guard. -/
theorem guard_to_seek (saved : Bool) (previous body : List Bool) :
    Edge (guardCfg saved (workLeft previous) body)
      (seekCfg saved previous.reverse [] (guardRow ++ body)) := by
  have rev := blocks_reverse previous
  rw [workLeft,rev]
  cases h : previous.reverse <;> cases saved <;>
    simp [Edge,guardCfg,seekCfg,cfg,sourceMachine,shuttle,seekOutput,TM1.step,TM1.stepAux,
      readBit,mv,jump,Function.iterate_succ_apply,guardRow,PSTRTMRawNat010.leftBlocks,
      PSTRTMIncrement009.blocks,Tape.mk₂]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
