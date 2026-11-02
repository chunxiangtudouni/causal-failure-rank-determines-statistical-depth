module
public import RootB236_Controller_ErasePort_Run002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ErasePort
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}
abbrev scale := Erase.scale

theorem interior_label (old : Erase.State C) (point : Label)
    (active : (configuration old).l=some point) (proper : point≠2) :
    ∃ selected : Erase.Label, old.l=some selected ∧ point=label selected := by
  cases chosen : old.l with
  | none =>
    have same : (2 : Label)=point := Option.some.inj (by simpa only [configuration,chosen,position] using active)
    exact False.elim (proper same.symm)
  | some selected =>
    have same : label selected=point := Option.some.inj (by simpa only [configuration,chosen,position] using active)
    exact ⟨selected,rfl,same.symm⟩

theorem work_internal (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bound : Nat) (current : State C) (within : WorkBound background context bound current)
    (point : Label) (active : current.l=some point) (proper : point≠2)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (member : node∈AuxWorkspace.nodes (program caller point) current.var current.stk) :
    node.1.1=context ∧
      (∀ stack, ¬Erase.Work stack → node.2 stack=background stack) ∧
      (∀ stack, (node.2 stack).length≤Erase.backgroundMass background+bound+2) ∧
      (AuxWorkspace.nodes (program caller point) current.var current.stk).length≤5 ∧
      ScannerStatement.clock (program caller point) current.var current.stk≤6*(Erase.backgroundMass background+bound+3) ∧
      ScannerClock.actions (program caller point)≤3 ∧ AuxWorkspace.pushes (program caller point)≤2 := by
  obtain ⟨old,oldBound,rfl⟩:=within
  obtain ⟨selected,_chosen,same⟩:=interior_label old point active proper
  subst point
  change node∈AuxWorkspace.nodes (program caller (label selected)) old.var old.stk at member
  rw [code_at,body_nodes] at member
  refine ⟨(Erase.nodes_context selected old.var old.stk node member).trans
    (Erase.work_context _ _ _ _ oldBound),?_,?_,?_,?_,?_,?_⟩
  · intro stack outside
    have nots : stack≠4 ∧ stack≠5 ∧ stack≠7 := by simpa only [Erase.Work,not_or] using outside
    exact (Erase.nodes_frame selected old.var old.stk stack outside node member).trans
      (Erase.work_frame _ _ _ _ oldBound stack nots.1 nots.2.1 nots.2.2)
  · exact Erase.work_internal_bound _ _ _ _ oldBound selected node member
  · simpa only [configuration,code_at,body_nodes] using Erase.program_nodes selected old.var old.stk
  · simpa only [configuration,code_at,body_clock] using Erase.work_clock_bound _ _ _ _ oldBound selected
  · simpa only [code_at,body_actions] using Erase.program_actions (C:=C) selected
  · simpa only [code_at,body_pushes] using Erase.program_pushes (C:=C) selected

theorem Facts.internal {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace.dropLast) (point : Label) (active : current.l=some point)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program caller point) current.var current.stk) :
    node.1.1=context ∧
      (∀ stack,¬Erase.Work stack → node.2 stack=background stack) ∧
      (∀ stack,(node.2 stack).length≤scale background skipped suffix) ∧
      (AuxWorkspace.nodes (program caller point) current.var current.stk).length≤5 ∧
      ScannerStatement.clock (program caller point) current.var current.stk≤6*scale background skipped suffix ∧
      ScannerClock.actions (program caller point)≤3 ∧ AuxWorkspace.pushes (program caller point)≤2 := by
  have proper : point≠2 := fun same => facts.no_early current member (same ▸ active)
  have result:=work_internal caller background context _ current
    (facts.boundary current (List.dropLast_subset trace member)) point active proper node inside
  refine ⟨result.1,result.2.1,?_,result.2.2.2.1,result.2.2.2.2.1,result.2.2.2.2.2⟩
  intro stack
  have bounded:=result.2.2.1 stack
  change (node.2 stack).length≤Erase.backgroundMass background+(2*skipped.length+suffix.length+1)+3
  omega

def statementClock (caller : Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program caller point) current.var current.stk
def traceClockSum (caller : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock caller)).sum

theorem statement_clock_configuration (caller : Statement C) (current : Erase.State C)
    (active : current.l≠none) : statementClock caller (configuration current)=Erase.statementClock current := by
  cases chosen : current.l with
  | none => exact False.elim (active chosen)
  | some selected => simp only [statementClock,configuration,chosen,position,code_at,body_clock,Erase.statementClock]

/-- Exact old/new SAME-witness clock equality; arbitrary caller2 is excluded. -/
theorem clock_sum_configuration (caller : Statement C) (trace : List (Erase.State C))
    (chain : trace.IsChain (fun a b => TM2.step Erase.program a=some b)) :
    traceClockSum caller (trace.map configuration)=Erase.traceClockSum trace := by
  simp only [traceClockSum,Erase.traceClockSum,←List.map_dropLast,List.map_map]
  congr 1
  apply List.map_congr_left
  intro current member
  exact statement_clock_configuration caller current (no_early_none trace chain current member)

theorem Facts.time_le {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final) :
    trace.length≤2*scale background skipped suffix := by
  rw [facts.time]
  change 2*skipped.length+3≤2*(Erase.backgroundMass background+(2*skipped.length+suffix.length+1)+3)
  omega

theorem Facts.clock_sum {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final) :
    traceClockSum caller trace≤12*(scale background skipped suffix)^2 := by
  have terms : ∀ clock∈trace.dropLast.map (statementClock caller),clock≤6*scale background skipped suffix := by
    intro clock member
    obtain ⟨current,inTrace,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp [statementClock,selected]
    | some point =>
      simp only [statementClock,selected]
      have node:=AuxWorkspace.endpoint_mem (program caller point) current.var current.stk
      exact (facts.internal current inTrace point selected _ node).2.2.2.2.1
  have sumBound : traceClockSum caller trace≤trace.dropLast.length*(6*scale background skipped suffix) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock caller)) (6*scale background skipped suffix) terms
  have count : trace.dropLast.length≤2*scale background skipped suffix := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time_le
  calc
    traceClockSum caller trace≤trace.dropLast.length*(6*scale background skipped suffix) := sumBound
    _≤(2*scale background skipped suffix)*(6*scale background skipped suffix) := Nat.mul_le_mul_right _ count
    _=12*(scale background skipped suffix)^2 := by ring

theorem Facts.charged {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final) :
    trace.length+traceClockSum caller trace≤14*(scale background skipped suffix)^2 := by
  have power : scale background skipped suffix≤(scale background skipped suffix)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (scale background skipped suffix)
      (Nat.succ_le_of_lt (Erase.scale_pos background skipped suffix))
  calc
    trace.length+traceClockSum caller trace≤2*(scale background skipped suffix)^2+12*(scale background skipped suffix)^2 :=
      Nat.add_le_add (facts.time_le.trans (Nat.mul_le_mul_left 2 power)) facts.clock_sum
    _=14*(scale background skipped suffix)^2 := by ring
end RootB236.Controller.ErasePort
