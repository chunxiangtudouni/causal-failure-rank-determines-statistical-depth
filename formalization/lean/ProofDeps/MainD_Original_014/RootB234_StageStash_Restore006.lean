module
public import RootB234_StageStash_Stash005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

/-- Every dirty field is physically cleared before its paired block is read. -/
theorem restore_prefix_run (memory : Store C) (parent background : Bank) (n : Nat) (small : n≤8) :
    ∃ current,Run (state (restorePoint n) memory (restoreBank parent background n))
      (state .restored current (restoreBank parent background 0))
      (fieldMass background n+fieldMass parent n+2*n) ∧ current.1=memory.1 := by
  induction n generalizing memory with
  | zero =>
    refine ⟨memory,?_,rfl⟩
    rw [show restorePoint 0=Label.restored by rfl]
    exact Run.refl (state .restored memory (restoreBank parent background 0))
  | succ n ih =>
    have inside : n<8 := by omega
    have one:=restore_one_run memory (restoreBank parent background (n+1)) (rom n)
      (parent (field (rom n))) (spool parent n) rfl
    change Run (state (.clear (rom n)) memory _) (state (nextRestore (rom n)) (clean memory)
      (two (restoreBank parent background (n+1)) 0 (field (rom n)) (spool parent n) (parent (field (rom n))))) _ at one
    rw [restore_current parent background n inside,next_restore n inside,restore_prefix parent background n inside] at one
    have point : restorePoint (n+1)=.clear (rom n) := by
      simp only [restorePoint,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
    rw [←point] at one
    obtain ⟨current,later,context⟩:=ih (clean memory) (by omega)
    have whole:=one.trans later
    refine ⟨current,?_,context⟩
    convert whole using 1
    simp only [fieldMass]
    omega

/-- Input0 may have any finite old tail; result15 and all nonwork stacks come from current background. -/
theorem restore_run (memory : Store C) (parent before : Bank) (spooled : before 0=spool parent 8) :
    ∃ current,Run (state (.clear 7) memory before) (state .restored current (restoreBank parent before 0))
      (fieldMass before 8+fieldMass parent 8+16) ∧ current.1=memory.1 := by
  obtain ⟨current,run,context⟩:=restore_prefix_run memory parent before 8 (Nat.le_refl 8)
  rw [restore_start parent before spooled] at run
  exact ⟨current,run,context⟩
end RootB234.StageStash
