module
public import RootB234_StageStash_Model003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def encBank (before : Bank) (i : Field) (bits spool : List Bool) : Bank := two before (field i) 0 bits spool

theorem enc_field (before : Bank) (i : Field) (bits spool : List Bool) : encBank before i bits spool (field i)=bits :=
  B23_6.DFSFrame.two_src _ _ _ (field_ne0 i) _ _
theorem enc_spool (before : Bank) (i : Field) (bits spool : List Bool) : encBank before i bits spool 0=spool := B23_6.DFSFrame.two_dst _ _ _ _ _
theorem enc_set_field (before : Bank) (i : Field) (bits spool value : List Bool) :
    Function.update (encBank before i bits spool) (field i) value=encBank before i value spool :=
  B23_6.DFSFrame.two_set_src _ _ _ (field_ne0 i) _ _ _
theorem enc_set_spool (before : Bank) (i : Field) (bits spool value : List Bool) :
    Function.update (encBank before i bits spool) 0 value=encBank before i bits value := B23_6.DFSFrame.two_set_dst _ _ _ _ _ _

theorem encode_empty (memory : Store C) (before : Bank) (i : Field) (spool : List Bool) :
    TM2.step source (state (.encode i) memory (encBank before i [] spool))=
      some (state (nextSave i) (clean memory) (encBank before i [] spool)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,enc_field,capture,clean,enc_set_field]

theorem encode_bit (memory : Store C) (before : Bank) (i : Field) (bit : Bool) (bits spool : List Bool) :
    TM2.step source (state (.encode i) memory (encBank before i (bit::bits) spool))=
      some (state (.encode i) (memory.1,true,bit) (encBank before i bits (true::bit::spool))) := by
  simp [state,TM2.step,source,program,TM2.stepAux,enc_field,enc_spool,capture,enc_set_field,enc_set_spool]

theorem encode_run (memory : Store C) (before : Bank) (i : Field) (bits spool : List Bool) :
    Run (state (.encode i) memory (encBank before i bits spool))
      (state (nextSave i) (clean memory) (encBank before i [] (pairs bits.reverse++spool))) (bits.length+1) := by
  induction bits generalizing memory spool with
  | nil =>
    simpa only [List.reverse_nil,B23_6.DFSFrame.pairs_nil,List.nil_append,List.length_nil] using
      Run.one (encode_empty memory before i spool) (active_state _ _ _ (by simp [Interior]))
  | cons bit bits ih =>
    simpa only [B23_6.DFSFrame.pairs_reverse_cons,List.length_cons,clean] using
      Run.cons (encode_bit memory before i bit bits spool) (active_state _ _ _ (by simp [Interior]))
        (ih (memory.1,true,bit) (true::bit::spool))

theorem header (memory : Store C) (before : Bank) (i : Field) :
    TM2.step source (state (.start ⟨i.val,by omega⟩) memory before)=
      some (state (.encode i) memory (Function.update before 0 (false::false::before 0))) := by
  simp [state,TM2.step,source,program,i.isLt,TM2.stepAux]

theorem save_one_run (memory : Store C) (before : Bank) (i : Field) :
    Run (state (.start ⟨i.val,by omega⟩) memory before) (state (nextSave i) (clean memory) (saveOne i before)) ((before (field i)).length+2) := by
  have head:=Run.one (header memory before i) (active_state _ _ _ (by simp [Interior]))
  have encoded:=encode_run memory before i (before (field i)) (false::false::before 0)
  have initial : encBank before i (before (field i)) (false::false::before 0)=Function.update before 0 (false::false::before 0) := by
    simp only [encBank,two,B23_6.DFSFrame.two,Function.update_eq_self]
  rw [initial] at encoded
  have tail : pairs (before (field i)).reverse++false::false::before 0=code (before (field i))++before 0 := by
    simp only [B23_6.DFSFrame.code,List.append_assoc,List.cons_append,List.nil_append]
  rw [tail] at encoded
  have whole:=head.trans encoded
  simpa only [encBank,saveOne,show 1+((before (field i)).length+1)=(before (field i)).length+2 by omega] using whole

theorem clear_empty (memory : Store C) (before : Bank) (i : Field) :
    TM2.step source (state (.clear i) memory (Function.update before (field i) []))=
      some (state (.decode i) (clean memory) (Function.update before (field i) [])) := by
  simp [state,TM2.step,source,program,TM2.stepAux,capture,clean]
theorem clear_bit (memory : Store C) (before : Bank) (i : Field) (bit : Bool) (bits : List Bool) :
    TM2.step source (state (.clear i) memory (Function.update before (field i) (bit::bits)))=
      some (state (.clear i) (memory.1,true,bit) (Function.update before (field i) bits)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,capture]
theorem clear_run_cells (memory : Store C) (before : Bank) (i : Field) (bits : List Bool) :
    Run (state (.clear i) memory (Function.update before (field i) bits))
      (state (.decode i) (clean memory) (Function.update before (field i) [])) (bits.length+1) := by
  induction bits generalizing memory with
  | nil => exact Run.one (clear_empty memory before i) (active_state _ _ _ (by simp [Interior]))
  | cons bit bits ih =>
    simpa only [List.length_cons,clean] using Run.cons (clear_bit memory before i bit bits)
      (active_state _ _ _ (by simp [Interior])) (ih (memory.1,true,bit))
theorem clear_run (memory : Store C) (before : Bank) (i : Field) :
    Run (state (.clear i) memory before) (state (.decode i) (clean memory) (Function.update before (field i) []))
      ((before (field i)).length+1) := by
  simpa only [Function.update_eq_self] using clear_run_cells memory before i (before (field i))

def decBank (before : Bank) (i : Field) (spool bits : List Bool) : Bank := two before 0 (field i) spool bits

theorem dec_spool (before : Bank) (i : Field) (spool bits : List Bool) : decBank before i spool bits 0=spool :=
  B23_6.DFSFrame.two_src _ _ _ (Ne.symm (field_ne0 i)) _ _
theorem dec_field (before : Bank) (i : Field) (spool bits : List Bool) : decBank before i spool bits (field i)=bits := B23_6.DFSFrame.two_dst _ _ _ _ _
theorem dec_set_spool (before : Bank) (i : Field) (spool bits value : List Bool) :
    Function.update (decBank before i spool bits) 0 value=decBank before i value bits :=
  B23_6.DFSFrame.two_set_src _ _ _ (Ne.symm (field_ne0 i)) _ _ _
theorem dec_set_field (before : Bank) (i : Field) (spool bits value : List Bool) :
    Function.update (decBank before i spool bits) (field i) value=decBank before i spool value := B23_6.DFSFrame.two_set_dst _ _ _ _ _ _

theorem decode_guard (memory : Store C) (before : Bank) (i : Field) (tail bits : List Bool) :
    TM2.step source (state (.decode i) memory (decBank before i (false::false::tail) bits))=
      some (state (nextRestore i) (clean memory) (decBank before i tail bits)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,dec_spool,capture,clean,dec_set_spool]
theorem decode_bit (memory : Store C) (before : Bank) (i : Field) (bit : Bool) (tail bits : List Bool) :
    TM2.step source (state (.decode i) memory (decBank before i (true::bit::tail) bits))=
      some (state (.decode i) (memory.1,true,bit) (decBank before i tail (bit::bits))) := by
  simp [state,TM2.step,source,program,TM2.stepAux,dec_spool,dec_field,capture,dec_set_spool,dec_set_field]

theorem decode_pairs_run (memory : Store C) (before : Bank) (i : Field) (bits tail target : List Bool) :
    Run (state (.decode i) memory (decBank before i (pairs bits++false::false::tail) target))
      (state (nextRestore i) (clean memory) (decBank before i tail (bits.reverse++target))) (bits.length+1) := by
  induction bits generalizing memory target with
  | nil =>
    simpa only [B23_6.DFSFrame.pairs_nil,List.nil_append,List.reverse_nil,List.length_nil] using
      Run.one (decode_guard memory before i tail target) (active_state _ _ _ (by simp [Interior]))
  | cons bit bits ih =>
    simpa only [B23_6.DFSFrame.pairs_cons,List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,clean] using
      Run.cons (decode_bit memory before i bit (pairs bits++false::false::tail) target)
        (active_state _ _ _ (by simp [Interior])) (ih (memory.1,true,bit) (bit::target))
theorem decode_code_run (memory : Store C) (before : Bank) (i : Field) (bits tail : List Bool) :
    Run (state (.decode i) memory (decBank before i (code bits++tail) []))
      (state (nextRestore i) (clean memory) (decBank before i tail bits)) (bits.length+1) := by
  simpa only [B23_6.DFSFrame.code,List.append_assoc,List.cons_append,List.nil_append,List.reverse_reverse,List.append_nil,List.length_reverse] using
    decode_pairs_run memory before i bits.reverse tail []

theorem restore_one_run (memory : Store C) (before : Bank) (i : Field) (bits tail : List Bool)
    (spooled : before 0=code bits++tail) :
    Run (state (.clear i) memory before) (state (nextRestore i) (clean memory) (decBank before i tail bits))
      ((before (field i)).length+bits.length+2) := by
  have cleared:=clear_run memory before i
  have decoded:=decode_code_run (clean memory) before i bits tail
  have initial : decBank before i (code bits++tail) []=Function.update before (field i) [] := by
    unfold decBank two B23_6.DFSFrame.two
    rw [←spooled,Function.update_eq_self]
  rw [initial] at decoded
  have whole:=cleared.trans decoded
  simpa only [clean,show (before (field i)).length+1+(bits.length+1)=(before (field i)).length+bits.length+2 by omega] using whole
end RootB234.StageStash
