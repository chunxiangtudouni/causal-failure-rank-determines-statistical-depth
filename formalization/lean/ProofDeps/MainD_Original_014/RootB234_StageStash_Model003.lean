module
public import RootB234_StageStash_Path002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open PaperProofs.Common.Native.PSTRWordBool
abbrev pairs := B23_6.DFSFrame.pairs
abbrev code := B23_6.DFSFrame.code
abbrev two := B23_6.DFSFrame.two

def rom (n : Nat) : Field := ⟨n%8,Nat.mod_lt n (by decide)⟩
def position (n : Nat) : Fin 9 := ⟨n%9,Nat.mod_lt n (by decide)⟩
def restorePoint (n : Nat) : Label := if n=0 then .restored else .clear (rom (n-1))

theorem rom_val (n : Nat) (small : n<8) : (rom n).val=n := Nat.mod_eq_of_lt small
theorem rom_index (i : Field) : rom i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
theorem position_val (n : Nat) (small : n<9) : (position n).val=n := Nat.mod_eq_of_lt small
theorem index_inverse (slot : Stack) (small : index slot<8) : field (rom (index slot))=slot := by
  fin_cases slot <;> simp_all [field,rom,index]
theorem index_equal (i : Field) (slot : Stack) (same : index slot=i.val) : slot=field i := by
  rw [←index_inverse slot (by rw [same];exact i.isLt),same,rom_index]
theorem next_save (n : Nat) (small : n<8) : nextSave (rom n)=.start (position (n+1)) := by
  unfold nextSave
  congr 1
  apply Fin.ext
  simp only [rom_val n small,position]
  exact (Nat.mod_eq_of_lt (by omega : n+1<9)).symm

theorem next_restore (n : Nat) (small : n<8) : nextRestore (rom n)=restorePoint n := by
  by_cases zero : n=0
  · subst n;rfl
  · simp only [nextRestore,rom_val n small,zero,restorePoint,ite_false,dite_false]
    congr 1
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (by omega : n-1<8)).symm

def spool (parent : Bank) : Nat → List Bool
  | 0 => parent 0
  | n+1 => code (parent (field (rom n)))++spool parent n

def fieldMass (parent : Bank) : Nat → Nat
  | 0 => 0
  | n+1 => (parent (field (rom n))).length+fieldMass parent n

def stashBank (parent : Bank) (n : Nat) : Bank := fun slot =>
  if slot=0 then spool parent n else if index slot<n then [] else parent slot

def saveOne (i : Field) (before : Bank) : Bank := two before (field i) 0 [] (code (before (field i))++before 0)

theorem stash_spool (parent : Bank) (n : Nat) : stashBank parent n 0=spool parent n := rfl

theorem stash_current (parent : Bank) (n : Nat) (small : n<8) : stashBank parent n (field (rom n))=parent (field (rom n)) := by
  simp only [stashBank,field_ne0,ite_false,field_index,rom_val n small,lt_self_iff_false]

theorem stash_zero (parent : Bank) : stashBank parent 0=parent := by
  funext slot
  by_cases s0 : slot=0
  · subst slot;rfl
  · simp only [stashBank,s0,ite_false,Nat.not_lt_zero]

theorem save_prefix (parent : Bank) (n : Nat) (small : n<8) : saveOne (rom n) (stashBank parent n)=stashBank parent (n+1) := by
  have rn:=(rom_val n small)
  funext slot
  by_cases s0 : slot=0
  · subst slot
    simp only [saveOne,two,B23_6.DFSFrame.two,Function.update_self,stash_spool,stash_current parent n small]
    rfl
  by_cases sf : slot=field (rom n)
  · subst slot
    simp only [saveOne,two,B23_6.DFSFrame.two,Function.update_of_ne (field_ne0 _),Function.update_self,
      stashBank,field_ne0,ite_false,field_index,rn,Nat.lt_succ_self,ite_true]
  have ne : index slot≠n := by intro equal;exact sf (index_equal (rom n) slot (equal.trans rn.symm))
  have same : index slot<n+1 ↔ index slot<n := by omega
  simp only [saveOne,two,B23_6.DFSFrame.two,Function.update_of_ne s0,Function.update_of_ne sf,stashBank,s0,ite_false,same]

def restoreBank (parent background : Bank) (n : Nat) : Bank := fun slot =>
  if slot=0 then spool parent n else if index slot<n then background slot else
    if index slot<8 then parent slot else background slot

theorem restore_current (parent background : Bank) (n : Nat) (small : n<8) :
    restoreBank parent background (n+1) (field (rom n))=background (field (rom n)) := by
  simp only [restoreBank,field_ne0,ite_false,field_index,rom_val n small,Nat.lt_succ_self,ite_true]

theorem restore_start (parent background : Bank) (spooled : background 0=spool parent 8) : restoreBank parent background 8=background := by
  funext slot
  by_cases s0 : slot=0
  · subst slot;exact spooled.symm
  · simp only [restoreBank,s0,ite_false]
    split_ifs <;> rfl

theorem restore_prefix (parent background : Bank) (n : Nat) (small : n<8) :
    two (restoreBank parent background (n+1)) 0 (field (rom n)) (spool parent n) (parent (field (rom n)))=
      restoreBank parent background n := by
  have rn:=(rom_val n small)
  funext slot
  by_cases s0 : slot=0
  · subst slot
    simp only [two,B23_6.DFSFrame.two,Function.update_of_ne (Ne.symm (field_ne0 _)),Function.update_self,restoreBank,ite_true]
  by_cases sf : slot=field (rom n)
  · subst slot
    simp only [two,B23_6.DFSFrame.two,Function.update_self,restoreBank,field_ne0,ite_false,field_index,rn,lt_self_iff_false,small,ite_true]
  have ne : index slot≠n := by intro equal;exact sf (index_equal (rom n) slot (equal.trans rn.symm))
  have same : index slot<n+1 ↔ index slot<n := by omega
  simp only [two,B23_6.DFSFrame.two,Function.update_of_ne sf,Function.update_of_ne s0,restoreBank,s0,ite_false,same]

theorem spool_length (parent : Bank) (n : Nat) : (spool parent n).length=(parent 0).length+2*fieldMass parent n+2*n := by
  induction n with
  | zero => simp only [spool,fieldMass];omega
  | succ n ih => simp only [spool,fieldMass,List.length_append,B23_6.DFSFrame.code_length,ih];omega

theorem stashed_fields (parent : Bank) (i : Field) : stashBank parent 8 (field i)=[] := by
  simp only [stashBank,field_ne0,ite_false,field_index,i.isLt,ite_true]

theorem restored_fields (parent background : Bank) (i : Field) : restoreBank parent background 0 (field i)=parent (field i) := by
  simp only [restoreBank,field_ne0,ite_false,Nat.not_lt_zero,field_index,i.isLt,ite_true]

theorem restored_tail (parent background : Bank) : restoreBank parent background 0 0=parent 0 := rfl
end RootB234.StageStash
