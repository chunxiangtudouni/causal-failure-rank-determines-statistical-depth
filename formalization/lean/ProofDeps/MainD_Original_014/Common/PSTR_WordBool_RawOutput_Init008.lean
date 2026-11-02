module

public import Common.PSTR_WordBool_RawOutput_Erase006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem encode_empty (bottom : Bool) :
    (FiniteTrackCodec.encode (bottom,fun _ : Fin 16 => (none : Option Bool))).toList =
      bottom :: List.replicate 32 false := by
  cases bottom <;> rfl

theorem encode_present (bottom bit : Bool) :
    (FiniteTrackCodec.encode
      (bottom,Function.update (fun _ : Fin 16 => (none : Option Bool)) 0 (some bit))).toList =
      bottom :: true :: bit :: List.replicate 30 false :=
  RawInit.row_encoding bottom bit

-- Mathlib's legacy Γ' is semireducible; this local proof option only lets
-- the elaborator compare that alias while rewriting the literal trInit.
set_option backward.isDefEq.respectTransparency false in
private theorem encoded_input_shape (bits : List Bool) :
    FiniteTrackCodec.encodedInput (0 : Fin 16) bits =
      match bits.reverse with
      | [] => true :: List.replicate 32 false
      | bit :: later => (true :: true :: bit :: List.replicate 30 false) ++ dataRows later := by
  unfold FiniteTrackCodec.encodedInput TM2to1.trInit
  dsimp only
  generalize h : bits.reverse = digits
  cases digits with
  | nil => rfl
  | cons bit later =>
    rw [List.map_cons,List.headI_cons,List.tail_cons,List.flatMap_cons,encode_present]
    apply congrArg (fun suffix => (true :: true :: bit :: List.replicate 30 false) ++ suffix)
    rw [List.flatMap_map]
    simp [encode_present,dataRows]
    rfl

theorem erase_initial_bottom (bits : List Bool) :
    (Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) bits)).write false =
      Tape.mk₁ (dataRows bits.reverse) := by
  rw [encoded_input_shape]
  generalize h : bits.reverse = digits
  cases digits with
  | nil =>
    change Tape.mk₂ [] (List.replicate 33 false)=Tape.mk₂ [] []
    exact blank_right [] 33
  | cons bit later =>
    change Tape.mk₂ [] ((false :: true :: bit :: List.replicate 30 false) ++
      later.flatMap (fun bit => false :: true :: bit :: List.replicate 30 false)) =
        Tape.mk₁ (dataRows (bit :: later))
    rfl

/-- This is a real negative33 movement from the known encoded input, a
real guard write, and a real return. No west room is a caller hypothesis. -/
theorem initial_step (bits : List Bool) :
    Edge (TM1.init (Γ := Bool) (Λ := Label) (σ := Unit)
      (FiniteTrackCodec.encodedInput (0 : Fin 16) bits)) (loopCfg [] bits.reverse) := by
  let tape := Tape.mk₁ (dataRows bits.reverse)
  have west : tape=Tape.mk₂ (List.replicate 33 false) (dataRows bits.reverse) := by
    dsimp [tape,Tape.mk₁]
    exact (blank_left [] (dataRows bits.reverse) 33).symm
  have left : (Tape.move .left)^[33] tape =
      Tape.mk₂ [] (List.replicate 33 false ++ dataRows bits.reverse) := by
    rw [west]
    simpa only [List.length_replicate,List.append_nil,List.reverse_replicate] using
      move_left_word (List.replicate 33 false) [] (dataRows bits.reverse)
  have right3 : (Tape.move .right)^[3]
      (Tape.mk₂ [] (List.replicate 33 false ++ dataRows bits.reverse)) =
      Tape.mk₂ [false,false,false] (List.replicate 30 false ++ dataRows bits.reverse) := by
    have split : List.replicate 33 false=[false,false,false] ++ List.replicate 30 false := rfl
    rw [split,List.append_assoc,show 3=([false,false,false] : List Bool).length by rfl,move_right_word]
    rfl
  have right30 : (Tape.move .right)^[30]
      (Tape.mk₂ [false,false,false] (true :: (List.replicate 29 false ++ dataRows bits.reverse))) =
      Tape.mk₂ guardRow.reverse (dataRows bits.reverse) := by
    change (Tape.move .right)^[30]
      (Tape.mk₂ [false,false,false] ((true :: List.replicate 29 false) ++ dataRows bits.reverse)) = _
    rw [show 30=(true :: List.replicate 29 false).length by rfl,move_right_word]
    rfl
  change some (TM1.stepAux (put false (mv 33 .left
    (mv 3 .right (put true (mv 30 .right (jump 1)))))) ()
      (Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) bits))) = _
  change some (TM1.stepAux (mv 33 .left (mv 3 .right (put true (mv 30 .right (jump 1))))) ()
    ((Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) bits)).write false)) = _
  rw [erase_initial_bottom,mv_step,left,mv_step,right3]
  change some (TM1.stepAux (mv 30 .right (jump 1)) ()
    (Tape.mk₂ [false,false,false] (true :: (List.replicate 29 false ++ dataRows bits.reverse)))) = _
  rw [mv_step,right30]
  change some (cfg 1 guardRow.reverse (dataRows bits.reverse))=some (loopCfg [] bits.reverse)
  unfold loopCfg workLeft doneRows
  change some (cfg 1 guardRow.reverse (dataRows bits.reverse))=
    some (cfg 1 (guardRow.reverse ++ List.replicate 2 false) (dataRows bits.reverse))
  unfold cfg
  rw [blank_left]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
