module

public import RootB234_PrepBudgetArchive_Run002
public import Common.PSTR_WordBool_ContextLift_041
public import Common.PSTR_WordVM_StackIso_042
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepBudgetArchive
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

@[simp] theorem backCells_length (digits : List Bool) : (backCells digits).length=2*digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih => simp [backCells,List.flatMap_cons] at *; omega

@[simp] theorem frontCells_length (digits : List Bool) : (frontCells digits).length=2*digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih => simp [frontCells,List.flatMap_cons] at *; omega

def Work (point : Stack) : Prop := point=1 ∨ point=15

def WorkBound (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  ∃ (point : Label) (bit flag pending : Bool) (source target : List Bool),
    current=state background point context bit flag pending source target ∧ source.length+target.length≤bound

theorem work_mono {background : Stack → List Bool} {context : C} {small large : Nat}
    {current : State C} (within : WorkBound background context small current) (larger : small≤large) :
    WorkBound background context large current := by
  obtain ⟨p,b,f,d,s,t,same,room⟩ := within
  exact ⟨p,b,f,d,s,t,same,room.trans larger⟩

theorem num_bound (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈numTrace background context bit flag pending older negative boundary left target,
      WorkBound background context (2*older.length+left.length+target.length+6) current := by
  induction older generalizing bit flag pending target with
  | nil =>
      intro current member
      simp [numTrace] at member
      rcases member with rfl | rfl | rfl <;>
        (refine ⟨_,_,_,_,_,_,rfl,?_⟩; simp only [List.length_cons,List.length_nil]; omega)
  | cons digit later ih =>
      intro current member
      rw [numTrace] at member
      rcases List.mem_cons.mp member with rfl | rest
      · refine ⟨_,_,_,_,_,_,rfl,?_⟩
        simp only [List.length_cons,List.length_append,backCells_length]
        omega
      · apply work_mono (ih digit false digit (true::pending::target) current rest)
        simp only [List.length_cons]; omega

theorem den_bound (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈denTrace background context bit flag pending later first near older negative boundary left target,
      WorkBound background context (2*later.length+2*older.length+left.length+target.length+10) current := by
  induction later generalizing bit flag pending target with
  | nil =>
      intro current member
      rw [denTrace] at member
      rcases List.mem_cons.mp member with rfl | rest
      · refine ⟨_,_,_,_,_,_,rfl,?_⟩
        simp only [denSource,List.length_cons,List.length_append,backCells_length,List.length_nil]
        omega
      rcases List.mem_cons.mp rest with rfl | rest
      · refine ⟨_,_,_,_,_,_,rfl,?_⟩
        simp only [List.length_cons,List.length_append,backCells_length,List.length_nil]; omega
      · apply work_mono (num_bound background context near false near older negative boundary left
          (false::false::true::first::target) current rest)
        simp only [List.length_cons,List.length_nil]; omega
  | cons digit rest ih =>
      intro current member
      rw [denTrace] at member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨_,_,_,_,_,_,rfl,?_⟩
        simp only [denSource,List.length_append,backCells_length,List.length_cons]; omega
      · apply work_mono (ih digit false pending (true::digit::target) current member)
        simp only [List.length_cons]; omega

def workSize (later older left target : List Bool) : Nat :=
  2*later.length+2*older.length+left.length+target.length+12

theorem actual_bound (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈actualTrace background context bit flag pending later first near older negative boundary left target,
      WorkBound background context (workSize later older left target) current := by
  intro current member
  rw [actualTrace] at member
  rcases List.mem_cons.mp member with rfl | rest
  · refine ⟨_,_,_,_,_,_,rfl,?_⟩
    simp only [denSource,List.length_cons,List.length_append,backCells_length,workSize]; omega
  · apply work_mono (den_bound background context bit flag pending later first near older negative boundary
      left (false::false::target) current rest)
    simp only [workSize,List.length_cons]; omega

def initialMass (background : Stack → List Bool) (later : List Bool) (first near : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) : Nat :=
  ∑ point : Stack,(bank background (true::true::denSource later first near negative boundary older left) target point).length

def scale (background : Stack → List Bool) (later : List Bool) (first near : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) : Nat :=
  initialMass background later first near older negative boundary left target+7

theorem initial_point (background : Stack → List Bool) (later : List Bool) (first near : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) (point : Stack) :
    (bank background (true::true::denSource later first near negative boundary older left) target point).length≤
      initialMass background later first near older negative boundary left target :=
  Finset.single_le_sum (f:=fun p : Stack =>
    (bank background (true::true::denSource later first near negative boundary older left) target p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)

theorem inputs_le_mass (background : Stack → List Bool) (later : List Bool) (first near : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    2*later.length+2*older.length+left.length+target.length+10≤
      initialMass background later first near older negative boundary left target := by
  let f := fun point : Stack =>
    (bank background (true::true::denSource later first near negative boundary older left) target point).length
  have small : (∑ point∈({1,15} : Finset Stack),f point)≤
      initialMass background later first near older negative boundary left target :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  simp [f,bank,denSource] at small
  omega

theorem work_actual_stack (background : Stack → List Bool) (context : C)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool)
    (current : State C)
    (within : WorkBound background context (workSize later older left target) current) (point : Stack) :
    (current.stk point).length ≤ initialMass background later first near older negative boundary left target+2 := by
  obtain ⟨p,b,f,d,s,t,rfl,room⟩ := within
  have mass := inputs_le_mass background later first near older negative boundary left target
  simp only [workSize] at room
  by_cases source : point=1
  · subst point; simp only [state,bank,ite_true]; omega
  by_cases destination : point=15
  · subst point; simp only [state,bank,show (15 : Stack)≠1 by decide,ite_false,ite_true]; omega
  have saved := initial_point background later first near older negative boundary left target point
  simp only [bank,source,destination,ite_false] at saved
  simp only [state,bank,source,destination,ite_false]
  omega

def baseProgram (point : Label) : TM2.Stmt Alphabet Label (Bool × Bool × Bool) :=
  if point=0 then
    .pop 1 (fun memory _ => memory) (.pop 1 (fun memory _ => memory)
      (.push 15 (fun _ => false) (.push 15 (fun _ => false) (.goto (fun _ => 1)))))
  else if point=1 then
    .pop 1 (fun memory value => (value.getD false,memory.2.1,memory.2.2))
      (.pop 1 (fun memory value => (memory.1,value.getD false,memory.2.2))
        (.push 15 Prod.fst (.push 15 (fun _ => true) (.branch (fun memory => memory.2.1)
          (.push 15 (fun _ => false) (.push 15 (fun _ => false) (.goto (fun _ => 2)))) (.goto (fun _ => 1))))))
  else if point=2 then
    .pop 1 (fun memory value => (value.getD false,memory.2.1,memory.2.2))
      (.pop 1 (fun memory value => (memory.1,value.getD false,memory.2.2))
        (.load (fun memory => (memory.1,memory.2.1,memory.1)) (.goto (fun _ => 3))))
  else if point=3 then
    .pop 1 (fun memory value => (value.getD false,memory.2.1,memory.2.2))
      (.pop 1 (fun memory value => (memory.1,value.getD false,memory.2.2))
        (.branch (fun memory => memory.2.1)
          (.push 1 (fun _ => true) (.push 1 Prod.fst
            (.push 15 (fun memory => memory.2.2) (.push 15 (fun _ => true) (.goto (fun _ => 4))))))
          (.push 15 (fun memory => memory.2.2) (.push 15 (fun _ => true)
            (.load (fun memory => (memory.1,memory.2.1,memory.1)) (.goto (fun _ => 3)))))))
  else .halt

theorem program_lift (point : Label) :
    program (C:=C) .halt point=ContextLift.statement (baseProgram point) := by
  fin_cases point <;> rfl

theorem nodes_context (point : Label) (memory : Store C) (slots : Stack → List Bool)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (member : node∈AuxWorkspace.nodes (program .halt point) memory slots) : node.1.1=memory.1 := by
  rcases memory with ⟨context,registers⟩
  rw [program_lift,ContextLift.nodes_configuration] at member
  obtain ⟨old,_present,same⟩ := List.mem_map.mp member
  subst node
  rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  fin_cases point <;> simp [program,StackIso.WritesOnly,Work]

theorem nodes_frame (label : Label) (memory : Store C) (slots : Stack → List Bool)
    (point : Stack) (untouched : ¬Work point)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (member : node∈AuxWorkspace.nodes (program .halt label) memory slots) : node.2 point=slots point :=
  StackIso.nodes_frame Work _ (program_writes label) memory slots point untouched node member

theorem fixed_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤6 := by
  fin_cases point <;> norm_num [program,ScannerClock.actions]

theorem fixed_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤4 := by
  fin_cases point <;> norm_num [program,AuxWorkspace.pushes]

end RootB234.PrepBudgetArchive
