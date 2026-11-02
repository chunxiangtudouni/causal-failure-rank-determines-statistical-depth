module
public import RootB236_Controller_RankCompare_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankCompare
open Turing
variable {C : Type*}

inductive Run (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C) (bound : Nat) :
    State C → State C → Nat → Prop where
  | refl {current : State C} (within : WorkBound bg context bound current) :
      Run lt eq gt bg context bound current current 0
  | step {before after final : State C} {steps : Nat} (point : Label)
      (within : WorkBound bg context bound before) (active : before.l=some point) (proper : Interior point)
      (edge : TM2.step (program lt eq gt) before=some after)
      (later : Run lt eq gt bg context bound after final steps) :
      Run lt eq gt bg context bound before final (steps+1)

theorem Run.append {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C} {bound : Nat}
    {before middle final : State C} {early later : Nat}
    (first : Run lt eq gt bg context bound before middle early)
    (last : Run lt eq gt bg context bound middle final later) :
    Run lt eq gt bg context bound before final (early+later) := by
  induction first with
  | refl _ => simpa only [Nat.zero_add] using last
  | step point within active proper edge _ ih =>
    simpa only [Nat.add_right_comm] using Run.step point within active proper edge (ih last)

theorem Run.actual {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C} {bound : Nat}
    {before final : State C} {steps : Nat} (run : Run lt eq gt bg context bound before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧
      trace.IsChain (fun a b => TM2.step (program lt eq gt) a=some b) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧
      (∀ current∈trace,WorkBound bg context bound current) ∧
      ∀ current∈trace.dropLast,∃ point,current.l=some point ∧ Interior point := by
  induction run with
  | refl within =>
    refine ⟨[_],rfl,List.isChain_singleton _,rfl,rfl,?_,?_⟩
    · intro current member
      have same:=List.mem_singleton.mp member
      subst current;exact within
    · simp
  | @step before after final steps point within active proper edge _ ih =>
    obtain ⟨trace,head,chain,last,length,bounds,interior⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp head
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_,?_⟩
    · change (after::tail).getLast?=some final;exact last
    · simp only [List.length_cons] at length ⊢;omega
    · intro current member
      rcases List.mem_cons.mp member with same | later
      · subst current;exact within
      · exact bounds current later
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with same | later
      · subst current;exact ⟨point,active,proper⟩
      · exact interior current later

theorem restore_left (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q bound : Nat) (mass : a+b+p+q≤bound) :
    Run lt eq gt bg context bound (state bg 1 context ha hb ord a b p q)
      (state bg 2 context false hb ord (a+p) b 0 q) (p+1) := by
  induction p generalizing a ha with
  | zero =>
    simp only [Nat.add_zero] at mass ⊢
    exact Run.step 1 (work_state _ _ _ _ _ _ _ _ _ _ _ mass) rfl (by simp [Interior])
      (step_left_end lt eq gt bg context ha hb ord a b q)
      (.refl (work_state _ _ _ _ _ _ _ _ _ _ _ mass))
  | succ p ih =>
    have next:=ih true (a+1) (by omega)
    have same : a+1+p=a+(p+1) := by omega
    rw [same] at next
    exact Run.step 1 (work_state _ _ _ _ _ _ _ _ _ _ _ mass) rfl (by simp [Interior])
      (step_left lt eq gt bg context ha hb ord a b p q) next

theorem restore_right (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q bound : Nat) (mass : a+b+p+q≤bound) :
    Run lt eq gt bg context bound (state bg 2 context ha hb ord a b p q)
      (state bg (returnLabel ord) context ha false ord a (b+q) p 0) (q+1) := by
  induction q generalizing b hb with
  | zero =>
    simp only [Nat.add_zero] at mass ⊢
    exact Run.step 2 (work_state _ _ _ _ _ _ _ _ _ _ _ mass) rfl (by simp [Interior])
      (step_right_end lt eq gt bg context ha hb ord a b p)
      (.refl (work_state _ _ _ _ _ _ _ _ _ _ _ mass))
  | succ q ih =>
    have next:=ih true (b+1) (by omega)
    have same : b+1+q=b+(q+1) := by omega
    rw [same] at next
    exact Run.step 2 (work_state _ _ _ _ _ _ _ _ _ _ _ mass) rfl (by simp [Interior])
      (step_right lt eq gt bg context ha hb ord a b p q) next

theorem restore_both (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q bound : Nat) (mass : a+b+p+q≤bound) :
    Run lt eq gt bg context bound (state bg 1 context ha hb ord a b p q)
      (state bg (returnLabel ord) context false false ord (a+p) (b+q) 0 0) (p+q+2) := by
  have left:=restore_left lt eq gt bg context ha hb ord a b p q bound mass
  have right:=restore_right lt eq gt bg context false hb ord (a+p) b 0 q bound (by omega)
  have joined:=left.append right
  have count : p+1+(q+1)=p+q+2 := by omega
  rw [count] at joined
  exact joined

def Correct (a b : Nat) : Ordering → Prop
  | .lt => a<b
  | .eq => a=b
  | .gt => b<a

theorem compare_run (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p bound : Nat) (mass : a+b+2*p≤bound) :
    ∃ steps result,Run lt eq gt bg context bound (state bg 0 context ha hb ord a b p p)
      (state bg (returnLabel result) context false false result (a+p) (b+p) 0 0) steps ∧
      Correct (a+p) (b+p) result ∧ steps≤2*(a+b+p)+3 := by
  induction a generalizing b p ha hb ord with
  | zero =>
    cases b with
    | zero =>
      have restore:=restore_both lt eq gt bg context false false .eq 0 0 p p bound (by omega)
      have run:=Run.step 0 (work_state bg 0 context ha hb ord 0 0 p p bound (by omega))
        rfl (by simp [Interior]) (step_eq lt eq gt bg context ha hb ord p p) restore
      exact ⟨_,.eq,run,rfl,by omega⟩
    | succ b =>
      have restore:=restore_both lt eq gt bg context false true .lt 0 b p (p+1) bound (by omega)
      have same : b+(p+1)=b+1+p := by omega
      rw [same] at restore
      have run:=Run.step 0 (work_state bg 0 context ha hb ord 0 (b+1) p p bound (by omega))
        rfl (by simp [Interior]) (step_lt lt eq gt bg context ha hb ord b p p) restore
      refine ⟨_,.lt,run,?_,by omega⟩
      change 0+p<b+1+p;omega
  | succ a ih =>
    cases b with
    | zero =>
      have restore:=restore_both lt eq gt bg context true false .gt a 0 (p+1) p bound (by omega)
      have same : a+(p+1)=a+1+p := by omega
      rw [same] at restore
      have run:=Run.step 0 (work_state bg 0 context ha hb ord (a+1) 0 p p bound (by omega))
        rfl (by simp [Interior]) (step_gt lt eq gt bg context ha hb ord a p p) restore
      refine ⟨_,.gt,run,?_,by omega⟩
      change 0+p<a+1+p;omega
    | succ b =>
      obtain ⟨steps,result,later,correct,time⟩:=ih true true ord b (p+1) (by omega)
      have sameA : a+(p+1)=a+1+p := by omega
      have sameB : b+(p+1)=b+1+p := by omega
      rw [sameA,sameB] at later correct
      refine ⟨steps+1,result,Run.step 0
        (work_state bg 0 context ha hb ord (a+1) (b+1) p p bound (by omega)) rfl (by simp [Interior])
        (step_both lt eq gt bg context ha hb ord a b p p) later,correct,by omega⟩

structure Facts (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b : Nat) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (state bg 0 context ha hb ord a b 0 0)
  chain : trace.IsChain (fun x y => TM2.step (program lt eq gt) x=some y)
  last : trace.getLast?=some final
  contents : ∃ result,Correct a b result ∧ final=state bg (returnLabel result) context false false result a b 0 0
  time : trace.length≤2*(a+b)+4
  boundary : ∀ current∈trace,WorkBound bg context (a+b) current
  interior : ∀ current∈trace.dropLast,∃ point,current.l=some point ∧ Interior point

theorem actual_facts (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b : Nat) :
    ∃ trace final,Facts lt eq gt bg context ha hb ord a b trace final := by
  obtain ⟨steps,result,run,correct,time⟩:=compare_run lt eq gt bg context ha hb ord a b 0 (a+b) (by omega)
  simp only [Nat.add_zero] at run correct time
  obtain ⟨trace,first,chain,last,length,boundary,interior⟩:=run.actual
  exact ⟨trace,_,⟨first,chain,last,⟨result,correct,rfl⟩,by omega,boundary,interior⟩⟩
end RootB236.Controller.RankCompare
