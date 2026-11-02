module
public import B23_6_DFSFrame_Cells004
public import B23_6_DFSFrame_Model003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def guarded (memory : Store C) : Store C := (memory.1,true,false)
def decBank (before : Bank) (i : Field) (spool bits : List Bool) : Bank := two before 13 (field i) spool bits
theorem dec_spool (before : Bank) (i : Field) (spool bits : List Bool) : decBank before i spool bits 13=spool :=
  two_src _ _ _ (Ne.symm (field_ne13 i)) _ _
theorem dec_field (before : Bank) (i : Field) (spool bits : List Bool) : decBank before i spool bits (field i)=bits :=
  two_dst _ _ _ _ _
theorem dec_set_spool (before : Bank) (i : Field) (spool bits value : List Bool) :
    Function.update (decBank before i spool bits) 13 value=decBank before i value bits :=
  two_set_src _ _ _ (Ne.symm (field_ne13 i)) _ _ _
theorem dec_set_field (before : Bank) (i : Field) (spool bits value : List Bool) :
    Function.update (decBank before i spool bits) (field i) value=decBank before i spool value := two_set_dst _ _ _ _ _ _

theorem decode_guard (memory : Store C) (before : Bank) (i : Field) (tail bits : List Bool) :
    TM2.step source (state (.decode i) memory (decBank before i (false::false::tail) bits))=
      some (state (nextPop i) (guarded memory) (decBank before i tail bits)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,dec_spool,RatDrop.capture,RatDrop.bit,guarded,dec_set_spool]
theorem decode_bit (memory : Store C) (before : Bank) (i : Field) (bit : Bool) (tail bits : List Bool) :
    TM2.step source (state (.decode i) memory (decBank before i (true::bit::tail) bits))=
      some (state (.decode i) (memory.1,true,bit) (decBank before i tail (bit::bits))) := by
  simp [state,TM2.step,source,program,TM2.stepAux,dec_spool,dec_field,RatDrop.capture,RatDrop.bit,dec_set_spool,dec_set_field]

theorem decode_pairs_run (memory : Store C) (before : Bank) (i : Field) (bits tail target : List Bool) :
    Run (state (.decode i) memory (decBank before i (pairs bits++false::false::tail) target))
      (state (nextPop i) (guarded memory) (decBank before i tail (bits.reverse++target))) (bits.length+1) := by
  induction bits generalizing memory target with
  | nil =>
    simpa only [pairs_nil,List.nil_append,List.reverse_nil,List.length_nil] using
      Run.one (decode_guard memory before i tail target) (active_state _ _ _ (by simp [Interior]))
  | cons bit bits ih =>
    simpa only [pairs_cons,List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,guarded] using
      Run.cons (decode_bit memory before i bit (pairs bits++false::false::tail) target)
        (active_state _ _ _ (by simp [Interior])) (ih (memory.1,true,bit) (bit::target))

theorem decode_code_run (memory : Store C) (before : Bank) (i : Field) (bits tail : List Bool) :
    Run (state (.decode i) memory (decBank before i (code bits++tail) []))
      (state (nextPop i) (guarded memory) (decBank before i tail bits)) (bits.length+1) := by
  simpa only [code,List.append_assoc,List.cons_append,List.nil_append,List.reverse_reverse,
    List.append_nil,List.length_reverse] using decode_pairs_run memory before i bits.reverse tail []

theorem dec_initial (before : Bank) (i : Field) (bits tail : List Bool)
    (spool : before 13=code bits++tail) :
    decBank before i (code bits++tail) []=Function.update before (field i) [] := by
  unfold decBank two
  rw [←spool,Function.update_eq_self]

theorem pop_one_run (memory : Store C) (before : Bank) (i : Field) (bits tail : List Bool)
    (spool : before 13=code bits++tail) :
    Run (state (.clearParent i) memory before)
      (state (nextPop i) (guarded memory) (decBank before i tail bits))
      ((before (field i)).length+bits.length+2) := by
  have clear:=clear_run (field i) (.clearParent i) (.decode i) rfl (by simp [Interior]) memory before
  have decode:=decode_code_run (clean memory) before i bits tail
  rw [dec_initial before i bits tail spool] at decode
  have all:=clear.trans decode
  have count : ((before (field i)).length+1)+(bits.length+1)=(before (field i)).length+bits.length+2:=by omega
  rw [count] at all
  simpa only [guarded,clean] using all

end B23_6.DFSFrame
