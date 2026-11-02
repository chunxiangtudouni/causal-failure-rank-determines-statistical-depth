module
public import B23_6_DFSFrame_Decode007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def popEntry (n : Nat) : Label := if n=0 then .readKind else .clearParent (rom (n-1))
theorem popEntry_succ (n : Nat) : popEntry (n+1)=.clearParent (rom n) := by simp [popEntry]
theorem nextPop_rom (n : Nat) (small : n<14) : nextPop (rom n)=popEntry n := by
  unfold nextPop popEntry
  simp only [rom_val n small]
  split_ifs with h
  · rfl
  · congr 1
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (by omega : n-1<14)).symm

theorem read_kind_step (memory : Store C) (before : Bank) (kind : Bool) (tail : List Bool) :
    TM2.step source (state .readKind memory (Function.update before 13 (kind::tail)))=
      some (state (.popDone kind) (clean memory) (Function.update before 13 tail)) := by
  cases kind <;> simp [state,TM2.step,source,program,TM2.stepAux,RatDrop.capture,RatDrop.bit,clean]

theorem restored_bank (before parent : Bank) (kind : Bool) (rank : List Bool)
    (spool : before 13=kind::parent 13) (actualRank : before 15=rank)
    (restored : ∀ i : Field,before (field i)=parent (field i)) :
    before=Function.update (restoreBank parent rank) 13 (kind::parent 13) := by
  funext slot
  by_cases s13 : slot=13
  · subst slot;simpa only [Function.update_self] using spool
  by_cases s15 : slot=15
  · subst slot;simpa only [restoreBank,Function.update_of_ne (by decide : (15 : Stack)≠13),Function.update_self] using actualRank
  obtain ⟨i,equal⟩ : ∃ i : Field,field i=slot:=⟨rom (index slot),field_index_inverse slot s13 s15⟩
  subst slot
  simpa only [restoreBank,Function.update_of_ne (field_ne13 i),Function.update_of_ne (field_ne15 i)] using restored i

theorem dec_other (before : Bank) (i : Field) (spool bits : List Bool) (slot : Stack)
    (not13 : slot≠13) (notField : slot≠field i) : decBank before i spool bits slot=before slot := by
  simp only [decBank,two,Function.update_of_ne notField,Function.update_of_ne not13]

theorem pop_suffix_run (memory : Store C) (parent : Bank) (kind : Bool) (rank : List Bool) (B : Nat)
    (parentCap : ∀ i : Field,(parent (field i)).length≤B) (n : Nat) (small : n≤14) (before : Bank)
    (spool : before 13=framePrefix parent kind n) (actualRank : before 15=rank)
    (restored : ∀ i : Field,n ≤ i.val → before (field i)=parent (field i))
    (currentCap : ∀ i : Field,(before (field i)).length≤B) :
    ∃ steps,Run (state (popEntry n) memory before)
      (state (.popDone kind) (clean memory) (restoreBank parent rank)) steps ∧
      steps≤n*(2*B+2)+1 := by
  induction n generalizing memory before with
  | zero =>
    have bankEq:=restored_bank before parent kind rank spool actualRank (fun i => restored i (by omega))
    rw [bankEq]
    have edge:=read_kind_step memory (restoreBank parent rank) kind (parent 13)
    have self : Function.update (restoreBank parent rank) 13 (parent 13)=restoreBank parent rank := by
      have at13 : restoreBank parent rank 13=parent 13 := rfl
      rw [←at13,Function.update_eq_self]
    rw [self] at edge
    exact ⟨1,Run.one edge (active_state _ _ _ (by decide)),by omega⟩
  | succ n ih =>
    have little : n<14:=by omega
    let i:=rom n
    have iv : i.val=n:=rom_val n little
    have leading : before 13=code (parent (field i))++framePrefix parent kind n:=spool
    have first:=pop_one_run memory before i (parent (field i)) (framePrefix parent kind n) leading
    let after:=decBank before i (framePrefix parent kind n) (parent (field i))
    have afterSpool : after 13=framePrefix parent kind n:=dec_spool _ _ _ _
    have afterRank : after 15=rank := by
      dsimp only [after]
      rw [dec_other before i _ _ 15 (by decide) (Ne.symm (field_ne15 i))]
      exact actualRank
    have afterRestored : ∀ j : Field,n≤j.val→after (field j)=parent (field j) := by
      intro j lower
      dsimp only [after]
      by_cases same : j=i
      · subst j;exact dec_field _ _ _ _
      · have distinct : field j≠field i:=fun eq => same (field_injective eq)
        rw [dec_other before i _ _ (field j) (field_ne13 j) distinct]
        have different : j.val≠n:=by intro eq;exact same (Fin.ext (eq.trans iv.symm))
        exact restored j (by omega)
    have afterCap : ∀ j : Field,(after (field j)).length≤B := by
      intro j
      dsimp only [after]
      by_cases same : j=i
      · subst j;simpa only [dec_field] using parentCap i
      · have distinct : field j≠field i:=fun eq => same (field_injective eq)
        rw [dec_other before i _ _ (field j) (field_ne13 j) distinct]
        exact currentCap j
    obtain ⟨m,tail,cap⟩:=ih (guarded memory) (by omega) after afterSpool afterRank afterRestored afterCap
    rw [nextPop_rom n little] at first
    rw [popEntry_succ]
    have whole:=first.trans tail
    refine ⟨(before (field i)).length+(parent (field i)).length+2+m,?_,?_⟩
    · simpa only [clean,guarded] using whole
    · have old:=currentCap i
      have new:=parentCap i
      nlinarith

theorem pop_boot_step (memory : Store C) (before : Bank) (flag : Bool) (tail : List Bool)
    (spool : before 13=flag::tail) :
    TM2.step source (state .popBoot memory before)=
      some (state (.clearParent 13) (memory.1,true,flag) (Function.update before 13 tail)) := by
  simp [state,TM2.step,source,program,TM2.stepAux,spool,RatDrop.capture]

theorem parent_cap_from_spool (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∀ i : Field,(parent (field i)).length≤RatInput.occupied child := by
  have cell:=RatInput.Encoder.point_mass child 13
  rw [spool,List.length_cons,frame_length] at cell
  intro i
  have room:=parent_field_mass parent i
  omega

theorem pop_run_caps (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) (B : Nat)
    (parentCap : ∀ i : Field,(parent (field i)).length≤B)
    (currentCap : ∀ i : Field,(child (field i)).length≤B) :
    ∃ steps,Run (state .popBoot memory child)
      (state (.popDone kind) (clean memory) (restoreBank parent (child 15))) steps ∧
      steps≤28*B+30 := by
  have boot:=Run.one (pop_boot_step memory child flag _ spool) (active_state _ _ _ (by decide))
  let before:=Function.update child 13 (framePrefix parent kind 14)
  have now : ∀ i : Field,(before (field i)).length≤B := by
    intro i
    simpa only [before,Function.update_of_ne (field_ne13 i)] using currentCap i
  obtain ⟨n,tail,cap⟩:=pop_suffix_run (memory.1,true,flag) parent kind (child 15) B
    parentCap 14 (by decide) before rfl rfl (by intro i h;omega) now
  have entry : popEntry 14=.clearParent 13:=rfl
  rw [entry] at tail
  refine ⟨1+n,?_,?_⟩
  · simpa only [clean] using boot.trans tail
  · omega

theorem pop_run (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∃ steps,Run (state .popBoot memory child)
      (state (.popDone kind) (clean memory) (restoreBank parent (child 15))) steps ∧
      steps≤30*(RatInput.occupied child+1) := by
  obtain ⟨n,run,cap⟩:=pop_run_caps memory parent child kind flag spool (RatInput.occupied child)
    (parent_cap_from_spool parent child kind flag spool) (fun i => RatInput.Encoder.point_mass child (field i))
  exact ⟨n,run,by omega⟩

end B23_6.DFSFrame
