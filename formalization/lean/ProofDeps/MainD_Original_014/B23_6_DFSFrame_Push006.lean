module
public import B23_6_DFSFrame_Encode005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

theorem seed_copy_run (memory : Store C) (before : Bank) (i : Field) (bits spool : List Bool) :
    Run (state (.copySeed i) memory (encBank before i [] spool bits.reverse))
      (state (nextSave i) (clean memory) (encBank before i bits spool [])) (bits.length+1) := by
  have run:=reverse_run (seedRoles i) (.copySeed i) (nextSave i) rfl (by simp [Interior]) memory
    (encBank before i [] spool bits.reverse)
  simpa only [seedRoles_source,seedRoles_target,enc_temporary,enc_field,List.reverse_reverse,List.append_nil,
    List.length_reverse,two,enc_set_temporary,enc_set_field] using run

theorem save_header_step (memory : Store C) (before : Bank) (i : Field) :
    TM2.step source (state (.saveStart ⟨i.val,by omega⟩) memory before)=
      some (state (.encode i) memory (Function.update before 13 (false::false::before 13))) := by
  simp [state,TM2.step,source,program,i.isLt,TM2.stepAux]

theorem enc_initial (before : Bank) (i : Field) (empty : before 15=[]) :
    encBank before i (before (field i)) (false::false::before 13) []=
      Function.update before 13 (false::false::before 13) := by
  have not13 : (13 : Stack)≠field i:=Ne.symm (field_ne13 i)
  have not15 : (15 : Stack)≠field i:=Ne.symm (field_ne15 i)
  funext slot
  by_cases a : slot=15 <;> by_cases b : slot=13 <;> by_cases c : slot=field i <;>
    simp_all [encBank]
theorem enc_saved (before : Bank) (i : Field) (_empty : before 15=[]) :
    encBank before i (if seed i then before (field i) else []) (code (before (field i))++before 13) []=saveOne i before := by
  have not13 : (13 : Stack)≠field i:=Ne.symm (field_ne13 i)
  have not15 : (15 : Stack)≠field i:=Ne.symm (field_ne15 i)
  funext slot
  by_cases a : slot=15 <;> by_cases b : slot=13 <;> by_cases c : slot=field i <;>
    simp_all [encBank,saveOne]

theorem save_one_run (memory : Store C) (before : Bank) (i : Field) (empty : before 15=[]) :
    ∃ n,Run (state (.saveStart ⟨i.val,by omega⟩) memory before)
      (state (nextSave i) (clean memory) (saveOne i before)) n ∧ n≤2*(before (field i)).length+3 := by
  have header:=Run.one (save_header_step memory before i) (active_state _ _ _ (by simp [Interior]))
  have encode:=encode_run memory before i (before (field i)) (false::false::before 13) []
  rw [enc_initial before i empty] at encode
  have spool : pairs (before (field i)).reverse++false::false::before 13=code (before (field i))++before 13 := by
    simp only [code,List.append_assoc,List.cons_append,List.nil_append]
  rw [spool] at encode
  cases h : seed i
  · simp only [h,Bool.false_eq_true,ite_false] at encode
    have all:=header.trans encode
    have finish : encBank before i [] (code (before (field i))++before 13) []=saveOne i before := by
      simpa only [h,Bool.false_eq_true,ite_false] using enc_saved before i empty
    rw [finish] at all
    exact ⟨_,all,by omega⟩
  · simp only [h,ite_true,List.append_nil] at encode
    have copy:=seed_copy_run (clean memory) before i (before (field i)) (code (before (field i))++before 13)
    have all:=header.trans (encode.trans copy)
    have finish : encBank before i (before (field i)) (code (before (field i))++before 13) []=saveOne i before := by
      simpa only [h,ite_true] using enc_saved before i empty
    simpa only [clean,finish] using (show ∃ n,Run (state (.saveStart ⟨i.val,by omega⟩) memory before)
      (state (nextSave i) (clean (clean memory)) (encBank before i (before (field i)) (code (before (field i))++before 13) [])) n ∧
      n≤2*(before (field i)).length+3 from ⟨_,all,by omega⟩)

theorem nextSave_rom (n : Nat) (small : n<14) : nextSave (rom n)=.saveStart (position (n+1)) := by
  unfold nextSave
  congr 1
  apply Fin.ext
  simp only [position,rom_val n small]
  exact (Nat.mod_eq_of_lt (by omega : n+1<15)).symm

theorem save_prefix_run (memory : Store C) (parent : Bank) (kind : Bool) (n : Nat) (small : n≤14) :
    ∃ steps,Run (state (.saveStart 0) (clean memory) (prefixBank parent kind 0))
      (state (.saveStart (position n)) (clean memory) (prefixBank parent kind n)) steps ∧
      steps≤2*massPrefix parent n+3*n := by
  induction n with
  | zero => exact ⟨0,Run.refl _,by simp only [massPrefix,Nat.mul_zero,Nat.add_zero,Nat.le_refl]⟩
  | succ n ih =>
    obtain ⟨a,first,acap⟩:=ih (by omega)
    obtain ⟨b,second,bcap⟩:=save_one_run (clean memory) (prefixBank parent kind n) (rom n) (prefix15 _ _ _)
    have startEq : (⟨(rom n).val,by omega⟩ : Fin 15)=position n := by
      apply Fin.ext
      rw [position_val n (by omega),rom_val n (by omega)]
    rw [startEq,nextSave_rom n (by omega),saveOne_prefix parent kind n (by omega)] at second
    simp only [clean] at first second ⊢
    rw [prefix_current parent kind n (by omega)] at bcap
    refine ⟨a+b,first.trans second,?_⟩
    simp only [massPrefix] at *
    omega

theorem push_header_step (memory : Store C) (parent : Bank) (kind : Bool) :
    TM2.step source (state (.pushHeader kind) (clean memory) (Function.update parent 15 []))=
      some (state (.saveStart 0) (clean memory) (prefixBank parent kind 0)) := by
  have banks : Function.update (Function.update parent 15 []) 13 (kind::parent 13)=prefixBank parent kind 0 := by
    rw [prefix_zero]
    exact (Function.update_comm (by decide : (13 : Stack)≠15) _ _ _).symm
  simp only [state,TM2.step,source,program,TM2.stepAux,Function.update_of_ne (by decide : (13 : Stack)≠15),banks]

theorem push_finish_step (memory : Store C) (parent : Bank) (kind : Bool) :
    TM2.step source (state (.saveStart (position 14)) (clean memory) (prefixBank parent kind 14))=
      some (state .pushDone (clean memory) (pushBank kind parent)) := by
  simp [state,TM2.step,source,program,position,TM2.stepAux,clean,pushBank,prefix13]

theorem push_run (memory : Store C) (parent : Bank) (kind : Bool) :
    ∃ steps,Run (state (.pushBoot kind) memory parent) (state .pushDone (clean memory) (pushBank kind parent)) steps ∧
      steps≤45*(RatInput.occupied parent+1) := by
  have clear:=clear_run 15 (.pushBoot kind) (.pushHeader kind) rfl (by simp [Interior]) memory parent
  have header:=Run.one (push_header_step memory parent kind) (active_state _ _ _ (by simp [Interior]))
  obtain ⟨n,save,cap⟩:=save_prefix_run memory parent kind 14 (by decide)
  have finish:=Run.one (push_finish_step memory parent kind) (active_state _ _ _ (by simp [Interior]))
  refine ⟨_,clear.trans (header.trans (save.trans finish)),?_⟩
  have mass:=massPrefix_bound parent 14
  have scratch:=RatInput.Encoder.point_mass parent 15
  omega

end B23_6.DFSFrame
