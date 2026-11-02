module

public import RootB236_Controller_Erase_Run002
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Common.PSTR_WordBool_ContextLift_041
public import Common.PSTR_WordVM_StackIso_042

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.Erase

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

def WorkBound (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  ∃ (point : Option Label) (present saved : Bool) (mask count parked : List Bool),
    current=state background point (context,present,saved) mask count parked ∧
      mask.length+count.length+parked.length ≤ bound

theorem work_mono {background : Stack → List Bool} {context : C} {small large : Nat}
    {current : State C} (within : WorkBound background context small current)
    (larger : small ≤ large) : WorkBound background context large current := by
  obtain ⟨point,present,saved,mask,count,parked,same,bound⟩ := within
  exact ⟨point,present,saved,mask,count,parked,same,bound.trans larger⟩

theorem restore_bound (background : Stack → List Bool) (context : C) (present saved : Bool)
    (parked mask count : List Bool) :
    ∀ current∈restoreTrace background context present saved parked mask count,
      WorkBound background context (2*parked.length+mask.length+count.length) current := by
  induction parked generalizing present saved mask count with
  | nil =>
      intro current member
      simp [restoreTrace] at member
      rcases member with rfl | rfl
      · exact ⟨some 1,present,saved,mask,count,[],rfl,by simp⟩
      · exact ⟨none,false,false,mask,count,[],rfl,by simp⟩
  | cons bit later ih =>
      intro current member
      rw [restoreTrace] at member
      rcases List.mem_cons.mp member with rfl | rest
      · refine ⟨some 1,present,saved,mask,count,bit::later,rfl,?_⟩
        simp only [List.length_cons]
        omega
      · apply work_mono (ih true bit (bit::mask) (true::count) current rest)
        simp only [List.length_cons]
        omega

theorem actual_bound (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix parked : List Bool) :
    ∀ current∈actualTrace background context present saved skipped head suffix parked,
      WorkBound background context (2*skipped.length+2*parked.length+suffix.length+1) current := by
  induction skipped generalizing present saved parked with
  | nil =>
      intro current member
      rw [actualTrace] at member
      rcases List.mem_cons.mp member with rfl | rest
      · refine ⟨some 0,present,saved,head::suffix,[],parked,rfl,?_⟩
        simp only [List.length_cons, List.length_nil]
        omega
      · apply work_mono (restore_bound background context false head parked (false::suffix) [] current rest)
        simp only [List.length_cons, List.length_nil]
        omega
  | cons bit later ih =>
      intro current member
      rw [actualTrace] at member
      rcases List.mem_cons.mp member with rfl | rest
      · refine ⟨some 0,present,saved,bit::later++head::suffix,
          List.replicate (later.length+1) true,parked,rfl,?_⟩
        simp only [List.length_cons, List.length_append, List.length_replicate]
        omega
      · apply work_mono (ih true bit (bit::parked) current rest)
        simp only [List.length_cons]
        omega

theorem work_context (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current) : current.var.1=context := by
  obtain ⟨point,present,saved,mask,count,parked,rfl,_⟩ := within
  rfl

theorem work_frame (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current)
    (point : Stack) (notMask : point≠4) (notCount : point≠5) (notParked : point≠7) :
    current.stk point=background point := by
  obtain ⟨label,present,saved,mask,count,parked,rfl,_⟩ := within
  exact cells_frame background mask count parked point notMask notCount notParked

theorem work_stack_bound (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current) (point : Stack) :
    (current.stk point).length ≤ (background point).length+bound := by
  obtain ⟨label,present,saved,mask,count,parked,rfl,mass⟩ := within
  by_cases atMask : point=4
  · subst point
    simp only [state,cells,ite_true]
    omega
  by_cases atCount : point=5
  · subst point
    simp only [state,cells,show (5 : Stack)≠4 by decide,ite_false,ite_true]
    omega
  by_cases atParked : point=7
  · subst point
    simp only [state,cells,show (7 : Stack)≠4 by decide,show (7 : Stack)≠5 by decide,ite_false,ite_true]
    omega
  · simp only [state,cells,atMask,atCount,atParked,ite_false]
    omega

def backgroundMass (background : Stack → List Bool) : Nat := ∑ point : Stack,(background point).length

theorem background_point_le (background : Stack → List Bool) (point : Stack) :
    (background point).length ≤ backgroundMass background := by
  exact Finset.single_le_sum (f := fun other : Stack => (background other).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)

theorem work_uniform_bound (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current) (point : Stack) :
    (current.stk point).length ≤ backgroundMass background+bound := by
  exact (work_stack_bound background context bound current within point).trans
    (Nat.add_le_add_right (background_point_le background point) bound)

theorem work_internal_bound (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current) (label : Label)
    (snapshot : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (member : snapshot∈AuxWorkspace.nodes (program label) current.var current.stk) (point : Stack) :
    (snapshot.2 point).length ≤ backgroundMass background+bound+2 := by
  have inside:=AuxWorkspace.node_bound (program label) current.var current.stk
    (backgroundMass background+bound) (work_uniform_bound background context bound current within)
    snapshot member point
  exact inside.trans (Nat.add_le_add_left (program_pushes label) _)

theorem work_clock_bound (background : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound background context bound current) (label : Label) :
    ScannerStatement.clock (program label) current.var current.stk ≤
      6*(backgroundMass background+bound+3) := by
  have clock:=ScannerClock.clock_bound (program label) current.var current.stk
    (backgroundMass background+bound) (work_uniform_bound background context bound current within)
  have actions:=program_actions (C := C) label
  have pushes:=program_pushes (C := C) label
  have left : 2*ScannerClock.actions (program (C := C) label) ≤ 6 := by omega
  have right : backgroundMass background+bound+AuxWorkspace.pushes (program (C := C) label)+1 ≤
      backgroundMass background+bound+3 := by omega
  exact clock.trans (Nat.mul_le_mul left right)

def Work (point : Stack) : Prop := point=4 ∨ point=5 ∨ point=7

def baseProgram (point : Label) : TM2.Stmt Alphabet Label (Bool × Bool) :=
  if point=0 then
    .pop 5 (fun memory value => (value.isSome,memory.2)) (.branch Prod.fst
      (.pop 4 (fun memory value => (memory.1,value.getD false))
        (.push 7 Prod.snd (.goto (fun _ => 0))))
      (.pop 4 (fun memory value => (memory.1,value.getD false))
        (.push 4 (fun _ => false) (.goto (fun _ => 1)))))
  else
    .pop 7 (fun _ value => (value.isSome,value.getD false)) (.branch Prod.fst
      (.push 4 Prod.snd (.push 5 (fun _ => true) (.goto (fun _ => 1)))) .halt)

theorem program_lift (point : Label) :
    program (C := C) point=ContextLift.statement (baseProgram point) := by
  fin_cases point <;> rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C := C) point) := by
  fin_cases point <;> simp [program,StackIso.WritesOnly,Work]

theorem nodes_context (point : Label) (memory : Store C) (slots : Stack → List Bool)
    (node : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (member : node∈AuxWorkspace.nodes (program point) memory slots) : node.1.1=memory.1 := by
  rcases memory with ⟨context,registers⟩
  rw [program_lift,ContextLift.nodes_configuration] at member
  obtain ⟨old,_present,same⟩ := List.mem_map.mp member
  subst node
  rfl

theorem nodes_frame (label : Label) (memory : Store C) (slots : Stack → List Bool)
    (point : Stack) (untouched : ¬Work point)
    (node : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (member : node∈AuxWorkspace.nodes (program label) memory slots) : node.2 point=slots point := by
  exact StackIso.nodes_frame Work _ (program_writes label) memory slots point untouched node member

theorem program_nodes (point : Label) (memory : Store C) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes (program point) memory slots).length ≤ 5 := by
  fin_cases point <;> norm_num [program,AuxWorkspace.nodes] <;> (split <;> simp)

end RootB236.Controller.Erase
