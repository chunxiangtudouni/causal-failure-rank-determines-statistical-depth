module
public import RootB236_Controller_RankMerge_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankMerge
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
/-- Actual steps only. The ACTIVE done body is never executed inside this path. -/
inductive Path (caller : Statement C) : State C → State C → Nat → Prop where
  | refl {current} : Path caller current current 0
  | step {before after final steps} (proper : before.l≠some done)
      (edge : TM2.step (program caller) before=some after) (later : Path caller after final steps) :
      Path caller before final (steps+1)
theorem Path.trans {caller : Statement C} {before middle final : State C} {early later : Nat}
    (first : Path caller before middle early) (last : Path caller middle final later) :
    Path caller before final (early+later) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | step proper edge _ ih => simpa only [Nat.add_right_comm] using Path.step proper edge (ih last)
theorem Path.actual {caller : Statement C} {before final : State C} {steps : Nat}
    (path : Path caller before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧
      trace.IsChain (fun x y => TM2.step (program caller) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧
      ∀ current∈trace.dropLast,current.l≠some done := by
  induction path with
  | refl => exact ⟨[_],rfl,List.isChain_singleton _,rfl,rfl,by simp⟩
  | @step before after final steps proper edge _ ih =>
    obtain ⟨trace,first,chain,last,length,interior⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp first
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_⟩
    · change (after::tail).getLast?=some final;exact last
    · simp only [List.length_cons] at length ⊢;omega
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact proper
      · exact interior current later
/-- Transport the same legacy chain; no stopped configuration is reset for free. -/
theorem Path.of_mapped {A : Type*} (caller : Statement C) (mapping : A → State C)
    (relation : A → A → Prop) (trace : List A) (before final : A)
    (first : trace.head?=some before) (chain : trace.IsChain relation) (last : trace.getLast?=some final)
    (edges : ∀ current∈trace.dropLast,∀ next,relation current next →
      TM2.step (program caller) (mapping current)=some (mapping next))
    (proper : ∀ current∈trace.dropLast,(mapping current).l≠some done) :
    Path caller (mapping before) (mapping final) (trace.length-1) := by
  induction trace generalizing before with
  | nil => cases first
  | cons head tail ih =>
    have same : head=before := Option.some.inj first
    subst head
    cases tail with
    | nil =>
      have same : before=final := Option.some.inj last
      subst final;exact Path.refl
    | cons next rest =>
      obtain ⟨edge,laterChain⟩:=List.isChain_cons_cons.mp chain
      have later:=ih next rfl laterChain (by exact last)
        (by intro current member other related
            exact edges current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member) other related)
        (by intro current member
            exact proper current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member))
      have now:=Path.step (proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self))
        (edges before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self) next edge) later
      simpa only [List.length_cons,Nat.add_sub_cancel] using now

def compareRoles (first : Bool) : Stack ≃ Stack := if first then limitRoles else Equiv.refl _
def compareMap (first : Bool) : RankCompare.Label → Label := if first then firstMap else secondMap
def compareLocal (first : Bool) (point : RankCompare.Label) :
    TM2.Stmt Alphabet RankCompare.Label (Store C) :=
  StackIso.statement (compareRoles first) (RankCompare.program .halt .halt .halt point)
def compareConfiguration (first : Bool) (before : RankCompare.State C) : State C :=
  LabelMap.configuration (compareMap first) (StackIso.configuration (compareRoles first) before)
private theorem roles_refl (body : TM2.Stmt Alphabet RankCompare.Label (Store C)) :
    StackIso.statement (Equiv.refl Stack) body=body := by
  induction body <;> simp_all [StackIso.statement]
theorem compare_code (caller : Statement C) (first : Bool) (point : RankCompare.Label) (proper : RankCompare.Interior point) :
    program caller (compareMap first point)=LabelMap.statement (compareMap first) (compareLocal first point) := by
  cases first
  · dsimp [compareMap,compareLocal,compareRoles]
    rw [roles_refl];exact second_code caller point proper
  · exact first_code caller point proper

theorem compare_edge (caller : Statement C) (first : Bool) (before after : RankCompare.State C)
    (point : RankCompare.Label) (active : before.l=some point) (proper : RankCompare.Interior point)
    (edge : TM2.step (RankCompare.program .halt .halt .halt) before=some after) :
    TM2.step (program caller) (compareConfiguration first before)=some (compareConfiguration first after) := by
  have code : ∀ other,(StackIso.configuration (compareRoles first) before).l=some other →
      program caller (compareMap first other)=LabelMap.statement (compareMap first) (compareLocal first other) := by
    intro other activeOther
    have same : other=point := Option.some.inj (activeOther.symm.trans active)
    subst other;exact compare_code caller first point proper
  unfold compareConfiguration
  rw [LabelMap.step_configuration_on (compareMap first) (compareLocal first) (program caller) _ code]
  rw [StackIso.step_configuration_on (compareRoles first) (RankCompare.program .halt .halt .halt)
    (compareLocal first) _ (by intros;rfl),edge]
  rfl

theorem actual_compare (caller : Statement C) (first : Bool) (background : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b : Nat) :
    ∃ steps result,RankCompare.Correct a b result ∧ steps≤2*(a+b)+3 ∧
      Path caller (compareConfiguration first (RankCompare.state background 0 context ha hb ord a b 0 0))
        (compareConfiguration first (RankCompare.state background (RankCompare.returnLabel result)
          context false false result a b 0 0)) steps := by
  obtain ⟨trace,final,facts⟩:=RankCompare.actual_facts (C:=C) .halt .halt .halt background context ha hb ord a b
  obtain ⟨result,correct,rfl⟩:=facts.contents
  have path:=Path.of_mapped caller (compareConfiguration first)
    (fun x y => TM2.step (RankCompare.program .halt .halt .halt) x=some y)
    trace _ _ facts.first facts.chain facts.last
    (by intro current member next edge
        obtain ⟨point,active,proper⟩:=facts.interior current member
        exact compare_edge caller first current next point active proper edge)
    (by intro current member
        obtain ⟨point,active,proper⟩:=facts.interior current member
        change current.l.map (compareMap first)≠some done
        rw [active,Option.map_some]
        cases first <;> fin_cases point <;> simp_all [RankCompare.Interior,compareMap,firstMap,secondMap,done,second])
  exact ⟨_,result,correct,by have time:=facts.time;omega,path⟩

theorem first_state (bg : Stack → List Bool) (context : C) (ha hb : Bool) (ord : Ordering)
    (limit a b : Nat) (point : RankCompare.Label) :
    compareConfiguration true (RankCompare.state (StackIso.slots limitRoles.symm (bank bg limit a b))
      point context ha hb ord a limit 0 0)=state (firstMap point) (context,ha,hb,ord) (bank bg limit a b) := by
  change (⟨some (firstMap point),(context,ha,hb,ord),_⟩ : State C)=⟨_,_,_⟩
  congr 1;funext slot;fin_cases slot <;> rfl
theorem second_state (bg : Stack → List Bool) (context : C) (ha hb : Bool) (ord : Ordering)
    (limit a b : Nat) (point : RankCompare.Label) :
    compareConfiguration false (RankCompare.state (bank bg limit a b)
      point context ha hb ord a b 0 0)=state (secondMap point) (context,ha,hb,ord) (bank bg limit a b) := by
  change (⟨some (secondMap point),(context,ha,hb,ord),_⟩ : State C)=⟨_,_,_⟩
  congr 1;funext slot;fin_cases slot <;> rfl

theorem first_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ steps result,RankCompare.Correct a limit result ∧ steps≤2*(a+limit)+3 ∧
      Path caller (state entry (context,ha,hb,ord) (bank bg limit a b))
        (state (firstMap (RankCompare.returnLabel result)) (context,false,false,result) (bank bg limit a b)) steps := by
  obtain ⟨steps,result,correct,time,path⟩:=actual_compare caller true
    (StackIso.slots limitRoles.symm (bank bg limit a b)) context ha hb ord a limit
  rw [first_state,first_state] at path
  exact ⟨steps,result,correct,time,path⟩
theorem second_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ steps result,RankCompare.Correct a b result ∧ steps≤2*(a+b)+3 ∧
      Path caller (state second (context,ha,hb,ord) (bank bg limit a b))
        (state (secondMap (RankCompare.returnLabel result)) (context,false,false,result) (bank bg limit a b)) steps := by
  obtain ⟨steps,result,correct,time,path⟩:=actual_compare caller false (bank bg limit a b) context ha hb ord a b
  rw [second_state,second_state] at path
  exact ⟨steps,result,correct,time,path⟩

def copyConfiguration (old : B23_4_RatWordPrep.WholeCopy.State (C×Ordering)) : State C :=
  LabelMap.configuration copyMap (StackIso.configuration (BestUpdate.copyRoles false)
    (StoreIso.configuration BestUpdate.storeIso old))
def copyState (background : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) : State C :=
  state (copyMap point) memory (BestUpdate.copyBank false background input backup scratch)
theorem copy_state (bg : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) :
    copyState bg point memory input backup scratch=copyConfiguration
      (B23_4_RatWordPrep.WholeCopy.state (StackIso.slots (BestUpdate.copyRoles false).symm bg) point
        (BestUpdate.storeIso.symm memory) input backup scratch) := by
  rw [copyState,BestUpdate.copyBank_eq]
  simp only [state,copyConfiguration,LabelMap.configuration,StackIso.configuration,StoreIso.configuration,
    B23_4_RatWordPrep.WholeCopy.state,Equiv.apply_symm_apply,Option.map_some]
theorem copy_edge (caller : Statement C) (before after : B23_4_RatWordPrep.WholeCopy.State (C×Ordering))
    (proper : before.l≠some .done)
    (edge : TM2.step (B23_4_RatWordPrep.WholeCopy.program .halt) before=some after) :
    TM2.step (program caller) (copyConfiguration before)=some (copyConfiguration after) := by
  have code : ∀ point,(StackIso.configuration (BestUpdate.copyRoles false)
      (StoreIso.configuration BestUpdate.storeIso before)).l=some point →
      program caller (copyMap point)=LabelMap.statement copyMap (copyLocal point) := by
    intro point active;exact copy_code caller point (by intro same;subst point;exact proper active)
  unfold copyConfiguration
  rw [LabelMap.step_configuration_on copyMap copyLocal (program caller) _ code]
  rw [StackIso.step_configuration_on (BestUpdate.copyRoles false)
    (StoreIso.machine BestUpdate.storeIso (B23_4_RatWordPrep.WholeCopy.program .halt)) copyLocal _ (by intros;rfl)]
  rw [StoreIso.step_configuration BestUpdate.storeIso (B23_4_RatWordPrep.WholeCopy.program .halt),edge]
  rfl

theorem actual_copy (caller : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) :
    Path caller (copyState bg .boot memory input backup scratch)
      (copyState bg .done (memory.1,true,true,memory.2.2.2) input (input.reverse++backup) scratch) (2*input.length+3) := by
  obtain ⟨trace,facts⟩:=B23_4_RatWordPrep.WholeCopy.actual_bounded
    (StackIso.slots (BestUpdate.copyRoles false).symm bg) (BestUpdate.storeIso.symm memory) input backup scratch
  have noEarly : ∀ current∈trace.dropLast,current.l≠some B23_4_RatWordPrep.WholeCopy.Label.done := by
    intro current member;exact (facts.proper current member).1
  have path:=Path.of_mapped caller copyConfiguration
    (fun x y => TM2.step (B23_4_RatWordPrep.WholeCopy.program .halt) x=some y)
    trace _ _ facts.first facts.chain facts.last
    (by intro current member next edge;exact copy_edge caller current next (noEarly current member) edge)
    (by intro current member
        have proper:=noEarly current member
        cases current with
        | mk position registers slots =>
          cases position with
          | none => change (none : Option Label)≠some done;intro impossible;cases impossible
          | some point => cases point <;> simp_all [copyConfiguration,LabelMap.configuration,
              StackIso.configuration,StoreIso.configuration,copyMap,done])
  rw [facts.count] at path
  have finalStore : BestUpdate.storeIso.symm (memory.1,true,true,memory.2.2.2)=
      ((BestUpdate.storeIso.symm memory).1,true,true) := rfl
  rw [←copy_state] at path
  rw [←finalStore,←copy_state] at path
  exact path
end RootB236.Controller.RankMerge
