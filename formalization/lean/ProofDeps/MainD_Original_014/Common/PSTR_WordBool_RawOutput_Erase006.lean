module

public import Common.PSTR_WordBool_RawOutput_Rows005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem blank_append_zeros (bits : List Bool) (count : Nat) :
    ListBlank.mk (bits ++ List.replicate count false)=ListBlank.mk bits := by
  apply Quotient.sound
  exact Or.inr ⟨count,rfl⟩

theorem blank_left (left right : List Bool) (count : Nat) :
    Tape.mk₂ (left ++ List.replicate count false) right=Tape.mk₂ left right := by
  unfold Tape.mk₂
  rw [blank_append_zeros]

theorem blank_right (left : List Bool) (count : Nat) :
    Tape.mk₂ left (List.replicate count false)=Tape.mk₂ left [] := by
  unfold Tape.mk₂
  rw [show ListBlank.mk (List.replicate count false)=ListBlank.mk ([] : List Bool) from blank_append_zeros [] count]

def currentRow (bit : Bool) : List Bool := bit :: List.replicate 32 false

/-- A marked source row is actually blanked and the head really travels
LEFT33. The preceding row is arbitrary33 data, including the guard row. -/
theorem erase_back (bit : Bool) (row left tail : List Bool) (size : row.length=33) :
    Edge (cfg 8 (row.reverse ++ left) (currentRow bit ++ tail))
      (cfg 8 left (row ++ List.replicate 33 false ++ tail)) := by
  let rowFront : List Bool := [bit,false,false]
  have shape : currentRow bit=rowFront ++ List.replicate 30 false := rfl
  have first : (Tape.move .right)^[3]
      (Tape.mk₂ (row.reverse ++ left) (currentRow bit ++ tail)) =
      Tape.mk₂ (rowFront.reverse ++ (row.reverse ++ left)) (List.replicate 30 false ++ tail) := by
    rw [shape,List.append_assoc,show 3=rowFront.length by rfl,move_right_word]
  have back : (Tape.move .left)^[3]
      (Tape.mk₂ (rowFront.reverse ++ (row.reverse ++ left)) (List.replicate 30 false ++ tail)) =
      Tape.mk₂ (row.reverse ++ left) (currentRow bit ++ tail) := by
    rw [show 3=rowFront.reverse.length by rfl,move_left_word,List.reverse_reverse]
    rw [shape,List.append_assoc]
  change some (TM1.stepAux (mv 3 .right (readBit
    (put false (mv 3 .left (put false (jump 9))))
    (mv 3 .left (put false (mv 33 .left (jump 8)))))) ()
      (Tape.mk₂ (row.reverse ++ left) (currentRow bit ++ tail))) = _
  rw [mv_step,first]
  change some (TM1.stepAux (mv 3 .left (put false (mv 33 .left (jump 8)))) ()
    (Tape.mk₂ (rowFront.reverse ++ (row.reverse ++ left)) (List.replicate 30 false ++ tail))) = _
  rw [mv_step,back]
  change some (TM1.stepAux (mv 33 .left (jump 8)) ()
    (Tape.mk₂ (row.reverse ++ left) (List.replicate 33 false ++ tail))) = _
  rw [mv_step,show 33=row.reverse.length by simpa using size.symm,move_left_word,List.reverse_reverse]
  simp only [jump,TM1.stepAux,cfg,List.append_assoc]

theorem erase_guard_tail (work tail : List Bool) :
    Edge (cfg 8 work (guardRow ++ tail))
      (cfg 9 work (List.replicate 33 false ++ tail)) := by
  simp [Edge,cfg,sourceMachine,guardRow,TM1.step,TM1.stepAux,readBit,put,mv,jump,
    Function.iterate_succ_apply,Tape.mk₂]

theorem erase_guard (work : List Bool) (padding : Nat) :
    Edge (cfg 8 work (guardRow ++ List.replicate padding false)) (cfg 9 work []) := by
  have edge := erase_guard_tail work (List.replicate padding false)
  have tape : Tape.mk₂ work (List.replicate 33 false ++ List.replicate padding false)=Tape.mk₂ work [] := by
    rw [← List.replicate_add,blank_right]
  simpa only [Edge,cfg,tape] using edge

def eraseCfg (bit : Bool) (older : Nat) (work tail : List Bool) : State :=
  cfg 8 ((doneRows older).reverse ++ guardRow.reverse ++ work) (currentRow bit ++ tail)

theorem erase_rows (bit : Bool) (older : Nat) (work tail : List Bool) :
    ∃ rest : List State, (eraseCfg bit older work tail :: rest).IsChain Edge ∧
      (eraseCfg bit older work tail :: rest).getLast? =
        some (cfg 8 work (guardRow ++ List.replicate (33*(older+1)) false ++ tail)) ∧
      rest.length=older+1 := by
  induction older generalizing bit tail with
  | zero =>
    let final := cfg 8 work (guardRow ++ List.replicate 33 false ++ tail)
    refine ⟨[final], ?_, rfl, rfl⟩
    · apply List.isChain_cons_cons.mpr
      exact ⟨erase_back bit guardRow work tail rfl,.singleton _⟩
  | succ older ih =>
    let left := (doneRows older).reverse ++ guardRow.reverse ++ work
    let next := eraseCfg true older work (List.replicate 33 false ++ tail)
    obtain ⟨rest,chain,last,clock⟩ := ih true (List.replicate 33 false ++ tail)
    have edge : Edge (eraseCfg bit (older+1) work tail) next := by
      simpa only [eraseCfg,doneRows_end,List.reverse_append,List.append_assoc,next,left,currentRow,doneRow] using
        erase_back bit doneRow left tail rfl
    have zeros : List.replicate (33*(older+1)) false ++ List.replicate 33 false =
        List.replicate (33*(older+1+1)) false := by
      rw [← List.replicate_add]
      congr 1
    have endEq : guardRow ++ List.replicate (33*(older+1)) false ++ (List.replicate 33 false ++ tail) =
        guardRow ++ List.replicate (33*(older+1+1)) false ++ tail := by
      simpa only [List.append_assoc] using congrArg (fun cells => guardRow ++ cells ++ tail) zeros
    refine ⟨next :: rest,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_⟩
    · simpa only [List.getLast?_cons_cons,endEq] using last
    · simp only [List.length_cons,clock]

theorem source_absent (left : List Bool) :
    Edge (cfg 1 left []) (cfg 2 (false :: left) []) ∧
      Edge (cfg 2 (false :: left) []) (cfg 8 left []) := by
  constructor <;>
    simp [Edge,cfg,sourceMachine,TM1.step,TM1.stepAux,readBit,mv,jump,
      Function.iterate_succ_apply,Tape.mk₂,PSTRTMRawNat010.blank_single_false]

/-- All consumed source markers and the owned guard are actually erased;
the normalized blank tail follows only after those writes have executed. -/
theorem erase_all (older : Nat) (work : List Bool) :
    ∃ rest : List State,
      (cfg 8 ((doneRows older).reverse ++ guardRow.reverse ++ work) [] :: rest).IsChain Edge ∧
      (cfg 8 ((doneRows older).reverse ++ guardRow.reverse ++ work) [] :: rest).getLast? =
        some (cfg 9 work []) ∧ rest.length=older+2 := by
  obtain ⟨rest,chain,last,clock⟩ := erase_rows false older work []
  have initial : eraseCfg false older work [] =
      cfg 8 ((doneRows older).reverse ++ guardRow.reverse ++ work) [] := by
    unfold eraseCfg cfg
    have row : currentRow false ++ ([] : List Bool)=List.replicate 33 false := rfl
    rw [row,blank_right]
  let middle := cfg 8 work (guardRow ++ List.replicate (33*(older+1)) false)
  have last' : (eraseCfg false older work [] :: rest).getLast?=some middle := by
    simpa [middle] using last
  have finalChain : [middle,cfg 9 work []].IsChain Edge :=
    List.isChain_cons_cons.mpr ⟨erase_guard work _,.singleton _⟩
  refine ⟨rest ++ [cfg 9 work []],?_,?_,?_⟩
  · have joined := NativeTrace.join_chain (eraseCfg false older work [] :: rest)
      middle [cfg 9 work []] last' chain finalChain
    simpa only [initial,List.cons_append] using joined
  · have joined := NativeTrace.join_last (eraseCfg false older work [] :: rest)
      middle [cfg 9 work []] last'
    simpa only [initial,List.cons_append,List.getLast?_cons_cons,List.getLast?_singleton] using joined
  · simp only [List.length_append,List.length_cons,List.length_nil,clock]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
