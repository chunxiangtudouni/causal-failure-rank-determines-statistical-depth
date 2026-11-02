module
public import RootB234_StageStash_Resources007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

namespace Public
/-- No initial empty stack assumption:15/4 and every nonwork stack are arbitrary. -/
theorem stash_actual (memory : Store C) (before : Bank) :
    ∃ path,Facts (.start 0) .saved memory before (stashBank before 8) path (state .saved (clean memory) (stashBank before 8)) ∧
      clockSum path≤65536*(scale before)^2 ∧ path.length+clockSum path≤65568*(scale before)^2 := by
  obtain ⟨path,facts⟩:=bounded_run (.start 0) .saved memory (clean memory) before (stashBank before 8)
    (fieldMass before 8+17) (stash_run memory before) (by
      have fields:=fieldMass_bound before 8
      dsimp only [scale];omega)
  exact ⟨path,facts,facts.clock_sum,facts.charged⟩

/-- Dirty work fields are really cleared;15 is the new result from current before, not the old stashed15. -/
theorem restore_actual (memory : Store C) (parent before : Bank) (spooled : before 0=spool parent 8) :
    ∃ path current,Facts (.clear 7) .restored memory before (restoreBank parent before 0) path
      (state .restored current (restoreBank parent before 0)) ∧
      clockSum path≤65536*(scale before)^2 ∧ path.length+clockSum path≤65568*(scale before)^2 := by
  obtain ⟨current,run,_context⟩:=restore_run memory parent before spooled
  have encoded:=point_mass before 0
  rw [spooled,spool_length] at encoded
  have fields:=fieldMass_bound before 8
  obtain ⟨path,facts⟩:=bounded_run (.clear 7) .restored memory current before (restoreBank parent before 0)
    (fieldMass before 8+fieldMass parent 8+16) run (by dsimp only [scale];omega)
  exact ⟨path,current,facts,facts.clock_sum,facts.charged⟩

theorem stash_ABI (before : Bank) :
    (∀ i : Field,stashBank before 8 (field i)=[]) ∧ stashBank before 8 0=spool before 8 ∧
    (spool before 8).length=(before 0).length+2*fieldMass before 8+16 :=
  ⟨stashed_fields before,rfl,spool_length before 8⟩

theorem restore_ABI (parent before : Bank) :
    (∀ i : Field,restoreBank parent before 0 (field i)=parent (field i)) ∧
    restoreBank parent before 0 0=parent 0 ∧ restoreBank parent before 0 15=before 15 ∧
    restoreBank parent before 0 4=before 4 ∧ restoreBank parent before 0 1=before 1 ∧
    restoreBank parent before 0 7=before 7 ∧ restoreBank parent before 0 8=before 8 ∧
    restoreBank parent before 0 9=before 9 ∧ restoreBank parent before 0 11=before 11 :=
  ⟨restored_fields parent before,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem store_card (C : Type*) [Fintype C] : Fintype.card (Store C)=4*Fintype.card C := by
  simp only [Store,Fintype.card_prod,Fintype.card_bool]
  omega

/-- The finite literal source/support/store precede all buffers, old0 tails and either old/new15. -/
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (fixed : Label → Statement C) (support : Finset Label),fixed=source ∧ support.card=35 ∧
      TM2.Supports fixed support ∧ Fintype.card (Store C)=4*Fintype.card C ∧
      (∀ (memory : Store C) (before : Bank),∃ path,
        Facts (.start 0) .saved memory before (stashBank before 8) path (state .saved (clean memory) (stashBank before 8))) ∧
      (∀ (memory : Store C) (parent before : Bank),before 0=spool parent 8 →∃ path current,
        Facts (.clear 7) .restored memory before (restoreBank parent before 0) path (state .restored current (restoreBank parent before 0))) := by
  refine ⟨source,Finset.univ,rfl,by simpa using label_count,supports .halt .halt,store_card C,?_,?_⟩
  · intro memory before
    obtain ⟨path,facts,_clock,_charge⟩:=stash_actual memory before
    exact ⟨path,facts⟩
  · intro memory parent before spooled
    obtain ⟨path,current,facts,_clock,_charge⟩:=restore_actual memory parent before spooled
    exact ⟨path,current,facts⟩

theorem caller_actual {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) {Ω : Type*} (mapping : Label → Ω)
    (target : Ω → TM2.Stmt Alphabet Ω (Store C))
    (agrees : ∀ point,Interior point → target (mapping point)=LabelMap.statement mapping (source point)) :
    (path.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping (state entry memory before)) ∧
    (path.map (LabelMap.configuration mapping)).IsChain (fun a b => TM2.step target a=some b) ∧
    (path.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) ∧
    (path.map (LabelMap.configuration mapping)).length=path.length ∧
    ∀ current∈path.map (LabelMap.configuration mapping),∃ old∈path,current=LabelMap.configuration mapping old ∧ current.var=old.var ∧ current.stk=old.stk := by
  exact LabelMap.actual_path_on mapping source target path _ _ facts.first facts.chain facts.last
    (by intro current member point active
        obtain ⟨old,selected,proper⟩:=facts.proper current member
        have same : point=old := Option.some.inj (active.symm.trans selected)
        subst point;exact agrees old proper)

theorem caller_noearly {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) {Ω : Type*} (mapping : Label ↪ Ω) :
    ∀ current∈(path.map (LabelMap.configuration mapping)).dropLast,
      current.l≠some (mapping .saved) ∧ current.l≠some (mapping .restored) := by
  intro current member
  rw [←List.map_dropLast] at member
  obtain ⟨old,inTrace,rfl⟩:=List.mem_map.mp member
  obtain ⟨point,active,proper⟩:=facts.proper old inTrace
  change old.l.map mapping≠some (mapping .saved) ∧ old.l.map mapping≠some (mapping .restored)
  rw [active,Option.map_some]
  exact ⟨fun eq => proper.1 (mapping.injective (Option.some.inj eq)),fun eq => proper.2 (mapping.injective (Option.some.inj eq))⟩

theorem boundary15 {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) (current : State C) (member : current∈path) : current.stk 15=before 15 :=
  (facts.boundaries current member).2.2 15 protected15

theorem internal15 {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) (current : State C) (member : current∈path.dropLast)
    (point : Label) (active : current.l=some point) (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (source point) current.var current.stk) : node.2 15=before 15 :=
  ((facts.internal current member point active).1 node inside).2.2 15 protected15
end Public
end RootB234.StageStash
