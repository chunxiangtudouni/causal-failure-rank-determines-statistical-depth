module
public import B23_6_DFSFrame_Cells004
public import B23_6_DFSFrame_Model003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def encBank (before : Bank) (i : Field) (bits spool temporary : List Bool) : Bank :=
  Function.update (Function.update (Function.update before (field i) bits) 13 spool) 15 temporary
theorem enc_field (before : Bank) (i : Field) (bits spool temporary : List Bool) :
    encBank before i bits spool temporary (field i)=bits := by
  simp only [encBank,Function.update_of_ne (field_ne15 i),Function.update_of_ne (field_ne13 i),Function.update_self]
theorem enc_spool (before : Bank) (i : Field) (bits spool temporary : List Bool) :
    encBank before i bits spool temporary 13=spool := rfl
theorem enc_temporary (before : Bank) (i : Field) (bits spool temporary : List Bool) :
    encBank before i bits spool temporary 15=temporary := rfl
theorem enc_set_field (before : Bank) (i : Field) (bits spool temporary value : List Bool) :
    Function.update (encBank before i bits spool temporary) (field i) value=encBank before i value spool temporary := by
  have not13 : (13 : Stack)≠field i:=Ne.symm (field_ne13 i)
  have not15 : (15 : Stack)≠field i:=Ne.symm (field_ne15 i)
  funext slot
  by_cases a : slot=field i <;> by_cases b : slot=13 <;> by_cases c : slot=15 <;>
    simp_all [encBank]
theorem enc_set_spool (before : Bank) (i : Field) (bits spool temporary value : List Bool) :
    Function.update (encBank before i bits spool temporary) 13 value=encBank before i bits value temporary := by
  funext slot
  by_cases a : slot=13 <;> by_cases b : slot=15 <;> simp_all [encBank]
theorem enc_set_temporary (before : Bank) (i : Field) (bits spool temporary value : List Bool) :
    Function.update (encBank before i bits spool temporary) 15 value=encBank before i bits spool value := by
  simp only [encBank,Function.update_idem]

theorem encode_empty (memory : Store C) (before : Bank) (i : Field) (spool temporary : List Bool) :
    TM2.step source (state (.encode i) memory (encBank before i [] spool temporary))=
      some (state (if seed i then .copySeed i else nextSave i) (clean memory) (encBank before i [] spool temporary)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,enc_field,RatDrop.capture,clean,enc_set_field]
theorem encode_cons (memory : Store C) (before : Bank) (i : Field) (bit : Bool)
    (bits spool temporary : List Bool) :
    TM2.step source (state (.encode i) memory (encBank before i (bit::bits) spool temporary))=
      some (state (.encode i) (memory.1,true,bit)
        (encBank before i bits (true::bit::spool) (if seed i then bit::temporary else temporary))) := by
  cases h : seed i <;>
    simp [state,TM2.step,source,program,TM2.stepAux,enc_field,RatDrop.capture,RatDrop.bit,keepSeed,h,
      enc_set_field,enc_set_spool,enc_set_temporary,enc_spool,enc_temporary]

theorem encode_run (memory : Store C) (before : Bank) (i : Field) (bits spool temporary : List Bool) :
    Run (state (.encode i) memory (encBank before i bits spool temporary))
      (state (if seed i then .copySeed i else nextSave i) (clean memory)
        (encBank before i [] (pairs bits.reverse++spool) (if seed i then bits.reverse++temporary else temporary)))
      (bits.length+1) := by
  induction bits generalizing memory spool temporary with
  | nil => simpa only [List.reverse_nil,pairs_nil,List.nil_append,List.length_nil,ite_self] using
      Run.one (encode_empty memory before i spool temporary) (active_state _ _ _ (by simp [Interior]))
  | cons bit bits ih =>
    have tail:=ih (memory.1,true,bit) (true::bit::spool) (if seed i then bit::temporary else temporary)
    have whole:=Run.cons (encode_cons memory before i bit bits spool temporary)
      (active_state _ _ _ (by simp [Interior])) tail
    rw [pairs_reverse_cons]
    cases h : seed i <;>
      simpa only [h,Bool.false_eq_true,ite_false,ite_true,List.length_cons,
        List.reverse_cons,List.append_assoc,List.singleton_append,clean] using whole

end B23_6.DFSFrame
