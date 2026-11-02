module
public import RootB236_Controller_DFSDriver_Resources017

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}
attribute [local irreducible] pushProfile actionProfile nodeProfile

theorem occupied_le (slots : Stack → List Bool) (bound : Nat) (bounded : ∀ slot,(slots slot).length≤bound) :
    (∑ slot : Stack,(slots slot).length)≤16*bound := by
  calc
    (∑ slot : Stack,(slots slot).length)≤∑ _slot : Stack,bound := Finset.sum_le_sum (fun slot _ => bounded slot)
    _=16*bound := by simp

private theorem charge_algebra (count coefficient : Nat) : count+1+count*coefficient≤(count+1)*(coefficient+1) := by nlinarith

/-- A peak is checked on each real boundary and is composed by a maximum, not by elapsed DFS visits. -/
inductive BoundedRun (finish : Statement C) (workspace : Nat) : State C → State C → Nat → Prop where
  | refl {current} (bounded : ∀ slot,(current.stk slot).length≤workspace) : BoundedRun finish workspace current current 0
  | step {before after final steps} (proper : before.l≠some done)
      (edge : TM2.step (program finish) before=some after)
      (bounded : ∀ slot,(before.stk slot).length≤workspace) (later : BoundedRun finish workspace after final steps) :
      BoundedRun finish workspace before final (steps+1)

theorem BoundedRun.run {finish : Statement C} {workspace : Nat} {before final : State C} {steps : Nat}
    (run : BoundedRun finish workspace before final steps) : Run finish before final steps := by
  induction run with
  | refl _ => exact .refl
  | step proper edge _ _ ih => exact .step proper edge ih

theorem BoundedRun.mono {finish : Statement C} {workspace larger : Nat} {before final : State C} {steps : Nat}
    (run : BoundedRun finish workspace before final steps) (le : workspace≤larger) :
    BoundedRun finish larger before final steps := by
  induction run with
  | refl bounded => exact .refl (fun slot => (bounded slot).trans le)
  | step proper edge bounded _ ih => exact .step proper edge (fun slot => (bounded slot).trans le) ih

theorem BoundedRun.trans {finish : Statement C} {workspace : Nat} {before middle final : State C} {early later : Nat}
    (first : BoundedRun finish workspace before middle early) (last : BoundedRun finish workspace middle final later) :
    BoundedRun finish workspace before final (early+later) := by
  induction first with
  | refl _ => simpa only [Nat.zero_add] using last
  | step proper edge bounded _ ih => simpa only [Nat.add_right_comm] using BoundedRun.step proper edge bounded (ih last)

/-- Each short callee is bounded directly from its own entry, before any global composition. -/
theorem Run.bounded {finish : Statement C} {before final : State C} {steps : Nat} (run : Run finish before final steps)
    (entry : Nat) (bounded : ∀ slot,(before.stk slot).length≤entry) :
    BoundedRun finish (entry+pushProfile C*steps) before final steps := by
  induction run generalizing entry with
  | refl => exact .refl (by simpa only [Nat.mul_zero,Nat.add_zero] using bounded)
  | @step before after final steps proper edge _ ih =>
    have next:=(step_resources finish before after entry proper edge bounded).2
    have rest:=ih (entry+pushProfile C) next
    have same : entry+pushProfile C+pushProfile C*steps=entry+pushProfile C*(steps+1) := by ring
    rw [same] at rest
    exact .step proper edge (fun slot => (bounded slot).trans (Nat.le_add_right _ _)) rest

theorem BoundedRun.actual {finish : Statement C} {workspace : Nat} {before final : State C} {steps : Nat}
    (run : BoundedRun finish workspace before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧ trace.IsChain (fun x y => TM2.step (program finish) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧ (∀ current∈trace.dropLast,current.l≠some done) ∧
      ∀ current∈trace,current.var.1=before.var.1 ∧ ∀ slot,(current.stk slot).length≤workspace := by
  induction run with
  | @refl current bounded =>
    refine ⟨[current],rfl,List.isChain_singleton _,rfl,rfl,by simp,?_⟩
    intro other member
    have same:=List.mem_singleton.mp member
    subst other
    exact ⟨rfl,bounded⟩
  | @step before after final steps proper edge bounded _ ih =>
    obtain ⟨trace,first,chain,last,length,interior,bounds⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp first
    have context:=(step_resources finish before after workspace proper edge bounded).1
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_,?_⟩
    · change (after::tail).getLast?=some final;exact last
    · simp only [List.length_cons] at length ⊢;omega
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact proper
      · exact interior current later
    · intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨rfl,bounded⟩
      · exact ⟨(bounds current later).1.trans context,(bounds current later).2⟩

def statementClock (finish : Statement C) (current : State C) : Nat :=
  match current.l with | none => 0 | some point => ScannerStatement.clock (program finish point) current.var current.stk
def clockSum (finish : Statement C) (trace : List (State C)) : Nat := (trace.dropLast.map (statementClock finish)).sum

theorem internal_resources (finish : Statement C) (workspace : Nat) (before : State C) (context : C)
    (proper : before.l≠some done) (readonly : before.var.1=context)
    (bounded : ∀ slot,(before.stk slot).length≤workspace) (point : Label) (active : before.l=some point) :
    (∀ node∈AuxWorkspace.nodes (program finish point) before.var before.stk,node.1.1=context ∧
      (∀ slot,(node.2 slot).length≤workspace+pushProfile C) ∧
      (∑ slot : Stack,(node.2 slot).length)≤16*(workspace+pushProfile C)) ∧
    (AuxWorkspace.nodes (program finish point) before.var before.stk).length≤nodeProfile C ∧
    ScannerClock.actions (program finish point)≤actionProfile C ∧ AuxWorkspace.pushes (program finish point)≤pushProfile C ∧
    ScannerStatement.clock (program finish point) before.var before.stk≤2*actionProfile C*(workspace+pushProfile C+1) := by
  have inside : point≠done := by intro same;subst point;exact proper active
  have sourceReadonly:=source_readonly (C:=C) point
  rw [←program_source finish point inside] at sourceReadonly
  refine ⟨?_,(syntax_nodes_count (program finish point) before.var before.stk).trans (nodes_le finish point inside),actions_le finish point inside,pushes_le finish point inside,?_⟩
  · intro node member
    have small : ∀ slot,(node.2 slot).length≤workspace+pushProfile C := fun slot =>
      (AuxWorkspace.node_bound (program finish point) before.var before.stk workspace bounded node member slot).trans (Nat.add_le_add_left (pushes_le finish point inside) workspace)
    refine ⟨(B23_4_RatWordPrep.RawGetter.nodes_readonly (fun memory : Store C => memory.1) (program finish point) sourceReadonly before.var before.stk node member).trans readonly,small,?_⟩
    exact occupied_le node.2 (workspace+pushProfile C) small
  · exact (ScannerClock.clock_bound (program finish point) before.var before.stk workspace bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (actions_le finish point inside)) (Nat.add_le_add_right (Nat.add_le_add_left (pushes_le finish point inside) workspace) 1))

theorem BoundedRun.clocked {finish : Statement C} {workspace : Nat} {before final : State C} {steps : Nat}
    (run : BoundedRun finish workspace before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧ trace.IsChain (fun x y => TM2.step (program finish) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧ (∀ current∈trace.dropLast,current.l≠some done) ∧
      (∀ current∈trace,current.var.1=before.var.1 ∧ ∀ slot,(current.stk slot).length≤workspace) ∧
      (∀ current∈trace.dropLast,∀ point,current.l=some point →
        (∀ node∈AuxWorkspace.nodes (program finish point) current.var current.stk,node.1.1=before.var.1 ∧
          (∀ slot,(node.2 slot).length≤workspace+pushProfile C) ∧
          (∑ slot : Stack,(node.2 slot).length)≤16*(workspace+pushProfile C)) ∧
        (AuxWorkspace.nodes (program finish point) current.var current.stk).length≤nodeProfile C ∧
        ScannerClock.actions (program finish point)≤actionProfile C ∧ AuxWorkspace.pushes (program finish point)≤pushProfile C ∧
        ScannerStatement.clock (program finish point) current.var current.stk≤2*actionProfile C*(workspace+pushProfile C+1)) ∧
      clockSum finish trace≤steps*(2*actionProfile C*(workspace+pushProfile C+1)) ∧
      trace.length+clockSum finish trace≤(steps+1)*(2*actionProfile C*(workspace+pushProfile C+1)+1) := by
  obtain ⟨trace,first,chain,last,length,proper,bounds⟩:=run.actual
  have internal : ∀ current∈trace.dropLast,∀ point,current.l=some point →
      (∀ node∈AuxWorkspace.nodes (program finish point) current.var current.stk,node.1.1=before.var.1 ∧
        (∀ slot,(node.2 slot).length≤workspace+pushProfile C) ∧
        (∑ slot : Stack,(node.2 slot).length)≤16*(workspace+pushProfile C)) ∧
      (AuxWorkspace.nodes (program finish point) current.var current.stk).length≤nodeProfile C ∧
      ScannerClock.actions (program finish point)≤actionProfile C ∧ AuxWorkspace.pushes (program finish point)≤pushProfile C ∧
      ScannerStatement.clock (program finish point) current.var current.stk≤2*actionProfile C*(workspace+pushProfile C+1) := by
    intro current member point active
    have boundary:=bounds current (List.dropLast_subset trace member)
    exact internal_resources finish workspace current before.var.1 (proper current member) boundary.1 boundary.2 point active
  have clocks : ∀ clock∈trace.dropLast.map (statementClock finish),clock≤2*actionProfile C*(workspace+pushProfile C+1) := by
    intro clock member
    obtain ⟨current,inTrace,rfl⟩:=List.mem_map.mp member
    cases active : current.l with
    | none => simp [statementClock,active]
    | some point =>
      simpa only [statementClock,active] using (internal current inTrace point active).2.2.2.2
  have sumBound : clockSum finish trace≤steps*(2*actionProfile C*(workspace+pushProfile C+1)) := by
    have total:=List.sum_le_length_nsmul (trace.dropLast.map (statementClock finish)) (2*actionProfile C*(workspace+pushProfile C+1)) clocks
    simpa only [clockSum,List.length_map,List.length_dropLast,length,Nat.add_sub_cancel,Nat.nsmul_eq_mul] using total
  refine ⟨trace,first,chain,last,length,proper,bounds,internal,sumBound,?_⟩
  rw [length]
  calc
    steps+1+clockSum finish trace≤steps+1+steps*(2*actionProfile C*(workspace+pushProfile C+1)) := Nat.add_le_add_left sumBound _
    _≤(steps+1)*(2*actionProfile C*(workspace+pushProfile C+1)+1) := charge_algebra steps _
end RootB236.Controller.DFSDriver.Machine

