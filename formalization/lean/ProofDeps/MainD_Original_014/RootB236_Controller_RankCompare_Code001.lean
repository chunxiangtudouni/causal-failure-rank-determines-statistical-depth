module
public import Common.PSTR_WordBool_ContextLift_041
public import Common.PSTR_WordVM_StackIso_042
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.Chain

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankCompare
open Turing PaperProofs.Common.Native.PSTRWordBool
abbrev Stack := Fin 16
abbrev Label := Fin 6
abbrev Alphabet (_ : Stack) := Bool
abbrev Registers := Bool × Bool × Ordering
abbrev Store (C : Type*) := C × Registers
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}
def unary (number : Nat) : List Bool := List.replicate number true
def returnLabel : Ordering → Label | .lt => 3 | .eq => 4 | .gt => 5
def captureLeft (memory : Registers) (value : Option Bool) : Registers :=
  (value.isSome,memory.2.1,memory.2.2)
def captureRight (memory : Registers) (value : Option Bool) : Registers :=
  (memory.1,value.isSome,memory.2.2)
def select (result : Ordering) (memory : Registers) : Registers :=
  (memory.1,memory.2.1,result)

/-- Only real pop-presence branches select Ordering; no numeric value is in store. -/
def core (point : Label) : TM2.Stmt Alphabet Label Registers :=
  if point=0 then
    .pop 9 captureLeft (.branch Prod.fst
      (.push 7 (fun _ => true) (.pop 10 captureRight (.branch (fun memory => memory.2.1)
        (.push 12 (fun _ => true) (.goto (fun _ => 0)))
        (.load (select .gt) (.goto (fun _ => 1))))))
      (.pop 10 captureRight (.branch (fun memory => memory.2.1)
        (.push 12 (fun _ => true) (.load (select .lt) (.goto (fun _ => 1))))
        (.load (select .eq) (.goto (fun _ => 1))))))
  else if point=1 then
    .pop 7 captureLeft (.branch Prod.fst
      (.push 9 (fun _ => true) (.goto (fun _ => 1))) (.goto (fun _ => 2)))
  else if point=2 then
    .pop 12 captureRight (.branch (fun memory => memory.2.1)
      (.push 10 (fun _ => true) (.goto (fun _ => 2)))
      (.goto (fun memory => returnLabel memory.2.2)))
  else .halt
def program (lt eq gt : Statement C) (point : Label) : Statement C :=
  if point=3 then lt else if point=4 then eq else if point=5 then gt
  else ContextLift.statement (core point)
def Interior (point : Label) : Prop := point=0 ∨ point=1 ∨ point=2
def Work (point : Stack) : Prop := point=7 ∨ point=9 ∨ point=10 ∨ point=12
def cells (background : Stack → List Bool) (left right savedLeft savedRight : Nat) : Stack → List Bool :=
  fun point => if point=9 then unary left else if point=10 then unary right else
    if point=7 then unary savedLeft else if point=12 then unary savedRight else background point
def state (background : Stack → List Bool) (point : Label) (context : C)
    (hasLeft hasRight : Bool) (order : Ordering) (left right savedLeft savedRight : Nat) : State C :=
  ⟨some point,(context,hasLeft,hasRight,order),cells background left right savedLeft savedRight⟩
def WorkBound (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  ∃ point hasLeft hasRight order left right savedLeft savedRight,
    current=state background point context hasLeft hasRight order left right savedLeft savedRight ∧
    left+right+savedLeft+savedRight≤bound
theorem work_state (background : Stack → List Bool) (point : Label) (context : C)
    (hasLeft hasRight : Bool) (order : Ordering) (left right savedLeft savedRight bound : Nat)
    (mass : left+right+savedLeft+savedRight≤bound) :
    WorkBound background context bound (state background point context hasLeft hasRight order left right savedLeft savedRight) :=
  ⟨point,hasLeft,hasRight,order,left,right,savedLeft,savedRight,rfl,mass⟩
theorem code_at (lt eq gt : Statement C) (point : Label) (proper : Interior point) :
    program lt eq gt point=ContextLift.statement (core point) := by
  fin_cases point <;> simp_all [Interior,program]
theorem step_both (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q : Nat) :
    TM2.step (program lt eq gt) (state bg 0 context ha hb ord (a+1) (b+1) p q)=
      some (state bg 0 context true true ord a b (p+1) (q+1)) := by
  simp only [state]
  change some (⟨some 0,(context,true,true,ord),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_eq (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (p q : Nat) :
    TM2.step (program lt eq gt) (state bg 0 context ha hb ord 0 0 p q)=
      some (state bg 1 context false false .eq 0 0 p q) := by
  change some (⟨some 1,(context,false,false,Ordering.eq),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_lt (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (b p q : Nat) :
    TM2.step (program lt eq gt) (state bg 0 context ha hb ord 0 (b+1) p q)=
      some (state bg 1 context false true .lt 0 b p (q+1)) := by
  simp only [state]
  change some (⟨some 1,(context,false,true,Ordering.lt),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_gt (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a p q : Nat) :
    TM2.step (program lt eq gt) (state bg 0 context ha hb ord (a+1) 0 p q)=
      some (state bg 1 context true false .gt a 0 (p+1) q) := by
  simp only [state]
  change some (⟨some 1,(context,true,false,Ordering.gt),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_left (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q : Nat) :
    TM2.step (program lt eq gt) (state bg 1 context ha hb ord a b (p+1) q)=
      some (state bg 1 context true hb ord (a+1) b p q) := by
  simp only [state]
  change some (⟨some 1,(context,true,hb,ord),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_left_end (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b q : Nat) :
    TM2.step (program lt eq gt) (state bg 1 context ha hb ord a b 0 q)=
      some (state bg 2 context false hb ord a b 0 q) := by
  change some (⟨some 2,(context,false,hb,ord),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_right (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p q : Nat) :
    TM2.step (program lt eq gt) (state bg 2 context ha hb ord a b p (q+1))=
      some (state bg 2 context ha true ord a (b+1) p q) := by
  simp only [state]
  change some (⟨some 2,(context,ha,true,ord),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl
theorem step_right_end (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b p : Nat) :
    TM2.step (program lt eq gt) (state bg 2 context ha hb ord a b p 0)=
      some (state bg (returnLabel ord) context ha false ord a b p 0) := by
  change some (⟨some (returnLabel ord),(context,ha,false,ord),_⟩ : State C)=_
  congr 1;congr 1
  funext point;fin_cases point <;> rfl

theorem core_actions (point : Label) : ScannerClock.actions (core point)≤4 := by
  fin_cases point <;> norm_num [core,ScannerClock.actions]
theorem core_pushes (point : Label) : AuxWorkspace.pushes (core point)≤2 := by
  fin_cases point <;> norm_num [core,AuxWorkspace.pushes]
private theorem closed_stmt (statement : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) statement := by
  induction statement with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ iy ino => exact ⟨iy,ino⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (lt eq gt : Statement C) : TM2.Supports (program lt eq gt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => closed_stmt (program lt eq gt point)⟩
end RootB236.Controller.RankCompare
