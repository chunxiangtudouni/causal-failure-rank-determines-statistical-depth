module
public import RootB234_StageStash_Cells004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

theorem stash_prefix_run (memory : Store C) (parent : Bank) (n : Nat) (small : n≤8) :
    ∃ current,Run (state (.start 0) memory parent) (state (.start (position n)) current (stashBank parent n))
      (fieldMass parent n+2*n) ∧ current.1=memory.1 := by
  induction n with
  | zero =>
    refine ⟨memory,?_,rfl⟩
    rw [show position 0=(0:Fin 9) by decide,stash_zero]
    exact Run.refl (state (.start 0) memory parent)
  | succ n ih =>
    have inside : n<8 := by omega
    obtain ⟨current,early,context⟩:=ih (by omega)
    have later:=save_one_run current (stashBank parent n) (rom n)
    have point : (⟨(rom n).val,by omega⟩ : Fin 9)=position n := by
      apply Fin.ext
      rw [rom_val n inside,position_val n (by omega)]
    rw [point,next_save n inside,stash_current parent n inside,save_prefix parent n inside] at later
    have whole:=early.trans later
    refine ⟨clean current,?_,context⟩
    convert whole using 1
    simp only [fieldMass]
    omega

theorem saved_edge (memory : Store C) (before : Bank) :
    TM2.step source (state (.start 8) memory before)=some (state .saved (clean memory) before) := rfl

theorem stash_run (memory : Store C) (parent : Bank) :
    Run (state (.start 0) memory parent) (state .saved (clean memory) (stashBank parent 8)) (fieldMass parent 8+17) := by
  obtain ⟨current,early,context⟩:=stash_prefix_run memory parent 8 (Nat.le_refl 8)
  have last:=Run.one (saved_edge current (stashBank parent 8)) (active_state _ _ _ (by simp [Interior]))
  have whole:=early.trans last
  change Run _ (state .saved (current.1,false,false) _) _ at whole
  rw [context] at whole
  simpa only [clean,Nat.add_assoc,show (2:Nat)*8+1=17 by decide] using whole

end RootB234.StageStash
