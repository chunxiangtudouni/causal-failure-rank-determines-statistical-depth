module
public import RootB236_Controller_RankCompare_Run002
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankCompare
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

def backgroundMass (bg : Stack → List Bool) : Nat := ∑ point : Stack,(bg point).length
def scale (bg : Stack → List Bool) (a b : Nat) : Nat := backgroundMass bg+(a+b)+3
theorem background_point_le (bg : Stack → List Bool) (point : Stack) :
    (bg point).length≤backgroundMass bg :=
  Finset.single_le_sum (f:=fun other : Stack => (bg other).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)
theorem work_context (bg : Stack → List Bool) (context : C) (bound : Nat) (current : State C)
    (within : WorkBound bg context bound current) : current.var.1=context := by
  obtain ⟨point,ha,hb,ord,a,b,p,q,rfl,_⟩:=within;rfl
theorem work_frame (bg : Stack → List Bool) (context : C) (bound : Nat) (current : State C)
    (within : WorkBound bg context bound current) (point : Stack) (outside : ¬Work point) :
    current.stk point=bg point := by
  obtain ⟨label,ha,hb,ord,a,b,p,q,rfl,_⟩:=within
  have nots : point≠7 ∧ point≠9 ∧ point≠10 ∧ point≠12 := by simpa only [Work,not_or] using outside
  simp only [state,cells,nots.1,nots.2.1,nots.2.2.1,nots.2.2.2,ite_false]
theorem work_stack (bg : Stack → List Bool) (context : C) (bound : Nat) (current : State C)
    (within : WorkBound bg context bound current) (point : Stack) :
    (current.stk point).length≤(bg point).length+bound := by
  obtain ⟨label,ha,hb,ord,a,b,p,q,rfl,mass⟩:=within
  simp only [state,cells]
  split_ifs <;> first | omega | (simp only [unary,List.length_replicate];omega)
theorem work_uniform (bg : Stack → List Bool) (context : C) (bound : Nat) (current : State C)
    (within : WorkBound bg context bound current) (point : Stack) :
    (current.stk point).length≤backgroundMass bg+bound :=
  (work_stack bg context bound current within point).trans (Nat.add_le_add_right (background_point_le bg point) bound)

theorem core_nodes (point : Label) (memory : Registers) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes (core point) memory slots).length≤7 := by
  fin_cases point
  · cases left : (slots 9).head? <;> cases right : (slots 10).head? <;>
      norm_num [core,AuxWorkspace.nodes,captureLeft,captureRight,select,left,right]
  · cases saved : (slots 7).head? <;> norm_num [core,AuxWorkspace.nodes,captureLeft,saved]
  · cases saved : (slots 12).head? <;> norm_num [core,AuxWorkspace.nodes,captureRight,saved]
  · norm_num [core,AuxWorkspace.nodes]
  · norm_num [core,AuxWorkspace.nodes]
  · norm_num [core,AuxWorkspace.nodes]
theorem program_actions (lt eq gt : Statement C) (point : Label) (proper : Interior point) :
    ScannerClock.actions (program lt eq gt point)≤4 := by
  rw [code_at lt eq gt point proper,ContextLift.statement_actions];exact core_actions point
theorem program_pushes (lt eq gt : Statement C) (point : Label) (proper : Interior point) :
    AuxWorkspace.pushes (program lt eq gt point)≤2 := by
  rw [code_at lt eq gt point proper,ContextLift.statement_pushes];exact core_pushes point
theorem program_nodes (lt eq gt : Statement C) (point : Label) (proper : Interior point)
    (memory : Store C) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes (program lt eq gt point) memory slots).length≤7 := by
  rcases memory with ⟨context,registers⟩
  rw [code_at lt eq gt point proper,ContextLift.nodes_configuration,List.length_map]
  exact core_nodes point registers slots
theorem program_writes (lt eq gt : Statement C) (point : Label) (proper : Interior point) :
    StackIso.WritesOnly Work (program lt eq gt point) := by
  rw [code_at lt eq gt point proper]
  fin_cases point <;> simp_all [Interior,core,ContextLift.statement,StackIso.WritesOnly,Work]
theorem nodes_context (lt eq gt : Statement C) (point : Label) (proper : Interior point)
    (memory : Store C) (slots : Stack → List Bool)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (member : node∈AuxWorkspace.nodes (program lt eq gt point) memory slots) : node.1.1=memory.1 := by
  rcases memory with ⟨context,registers⟩
  rw [code_at lt eq gt point proper,ContextLift.nodes_configuration] at member
  obtain ⟨old,_present,same⟩:=List.mem_map.mp member
  subst node;rfl
theorem work_clock (lt eq gt : Statement C) (bg : Stack → List Bool) (context : C) (bound : Nat)
    (current : State C) (within : WorkBound bg context bound current) (point : Label) (proper : Interior point) :
    ScannerStatement.clock (program lt eq gt point) current.var current.stk≤8*(backgroundMass bg+bound+3) := by
  have clock:=ScannerClock.clock_bound (program lt eq gt point) current.var current.stk
    (backgroundMass bg+bound) (work_uniform bg context bound current within)
  have actions:=program_actions lt eq gt point proper
  have pushes:=program_pushes lt eq gt point proper
  exact clock.trans (Nat.mul_le_mul (by omega) (by omega))

theorem Facts.context {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) (current : State C) (member : current∈trace) :
    current.var.1=context := work_context _ _ _ _ (facts.boundary current member)
theorem Facts.frame {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) (current : State C) (member : current∈trace)
    (point : Stack) (outside : ¬Work point) : current.stk point=bg point :=
  work_frame _ _ _ _ (facts.boundary current member) point outside
theorem Facts.internal {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final)
    (current : State C) (member : current∈trace.dropLast) (point : Label) (active : current.l=some point)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program lt eq gt point) current.var current.stk) :
    node.1.1=context ∧ (∀ stack,¬Work stack → node.2 stack=bg stack) ∧
      (∀ stack,(node.2 stack).length≤scale bg a b) ∧
      (AuxWorkspace.nodes (program lt eq gt point) current.var current.stk).length≤7 ∧
      ScannerStatement.clock (program lt eq gt point) current.var current.stk≤8*scale bg a b ∧
      ScannerClock.actions (program lt eq gt point)≤4 ∧ AuxWorkspace.pushes (program lt eq gt point)≤2 := by
  obtain ⟨selected,atSelected,proper⟩:=facts.interior current member
  have same : point=selected := Option.some.inj (active.symm.trans atSelected)
  subst point
  have inTrace:=List.dropLast_subset trace member
  have within:=facts.boundary current inTrace
  refine ⟨(nodes_context lt eq gt selected proper current.var current.stk node inside).trans
    (facts.context current inTrace),?_,?_,program_nodes lt eq gt selected proper current.var current.stk,
    work_clock lt eq gt bg context (a+b) current within selected proper,program_actions lt eq gt selected proper,
    program_pushes lt eq gt selected proper⟩
  · intro stack outside
    exact (StackIso.nodes_frame Work _ (program_writes lt eq gt selected proper) current.var current.stk
      stack outside node inside).trans (facts.frame current inTrace stack outside)
  · intro stack
    have bound:=AuxWorkspace.node_bound (program lt eq gt selected) current.var current.stk
      (backgroundMass bg+(a+b)) (work_uniform bg context (a+b) current within) node inside stack
    have pushes:=program_pushes lt eq gt selected proper
    change (node.2 stack).length≤backgroundMass bg+(a+b)+3
    omega
theorem Facts.restored {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) :
    final.stk 9=unary a ∧ final.stk 10=unary b ∧ final.stk 7=[] ∧ final.stk 12=[] := by
  obtain ⟨result,_correct,rfl⟩:=facts.contents
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem Facts.ports {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) :
    (final.l=some 3 ↔ a<b) ∧ (final.l=some 4 ↔ a=b) ∧ (final.l=some 5 ↔ b<a) := by
  obtain ⟨result,correct,rfl⟩:=facts.contents
  cases result <;> simp only [Correct] at correct <;> norm_num [state,returnLabel] <;> omega

def statementClock (lt eq gt : Statement C) (current : State C) : Nat :=
  match current.l with | none => 0 | some point => ScannerStatement.clock (program lt eq gt point) current.var current.stk
def traceClockSum (lt eq gt : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock lt eq gt)).sum
theorem Facts.time_le {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) : trace.length≤2*scale bg a b := by
  have time:=facts.time
  change trace.length≤2*(backgroundMass bg+(a+b)+3)
  omega
theorem Facts.clock_sum {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) :
    traceClockSum lt eq gt trace≤16*(scale bg a b)^2 := by
  have terms : ∀ clock∈trace.dropLast.map (statementClock lt eq gt),clock≤8*scale bg a b := by
    intro clock member
    obtain ⟨current,inTrace,rfl⟩:=List.mem_map.mp member
    cases active : current.l with
    | none => simp [statementClock,active]
    | some point =>
      simp only [statementClock,active]
      exact (facts.internal current inTrace point active _ (AuxWorkspace.endpoint_mem _ _ _)).2.2.2.2.1
  have sumBound : traceClockSum lt eq gt trace≤trace.dropLast.length*(8*scale bg a b) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock lt eq gt)) (8*scale bg a b) terms
  have count : trace.dropLast.length≤2*scale bg a b := by
    rw [List.length_dropLast];exact (Nat.sub_le trace.length 1).trans facts.time_le
  calc
    traceClockSum lt eq gt trace≤trace.dropLast.length*(8*scale bg a b) := sumBound
    _≤(2*scale bg a b)*(8*scale bg a b) := Nat.mul_le_mul_right _ count
    _=16*(scale bg a b)^2 := by ring
theorem Facts.charged {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts lt eq gt bg context ha hb ord a b trace final) :
    trace.length+traceClockSum lt eq gt trace≤18*(scale bg a b)^2 := by
  have positive : 0<scale bg a b := by change 0<backgroundMass bg+(a+b)+3;omega
  have power : scale bg a b≤(scale bg a b)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (scale bg a b) (Nat.succ_le_of_lt positive)
  calc
    trace.length+traceClockSum lt eq gt trace≤2*(scale bg a b)^2+16*(scale bg a b)^2 :=
      Nat.add_le_add (facts.time_le.trans (Nat.mul_le_mul_left 2 power)) facts.clock_sum
    _=18*(scale bg a b)^2 := by ring
end RootB236.Controller.RankCompare
