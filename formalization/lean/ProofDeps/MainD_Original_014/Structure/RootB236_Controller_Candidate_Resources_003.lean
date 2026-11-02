module
public import Structure.RootB236_Controller_Candidate_Run_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing
open PaperProofs.Common.Native
open PSTRWordBool
abbrev mass := Bitwise.backgroundMass

theorem valid_stack (bg : Stack → List Bool) (bound : Nat) (current : ScanState)
    (valid : Valid bg bound current) (point : Stack) :
    (current.stk point).length≤mass bg+bound :=
  (valid.1 point).trans (Nat.add_le_add_right (Bitwise.background_point_le bg point) bound)

theorem scanner_resources (bg : Stack → List Bool) (bound : Nat) (current : ScanState)
    (valid : Valid bg bound current) (label : ScanLabel)
    (snapshot : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store))
    (node : snapshot∈AuxWorkspace.nodes (scanner label) current.var current.stk) :
    ScannerClock.actions (scanner label)≤3 ∧ AuxWorkspace.pushes (scanner label)≤2 ∧
    ScannerStatement.clock (scanner label) current.var current.stk≤6*(mass bg+bound+3) ∧
    (∀ point, (snapshot.2 point).length≤mass bg+bound+2) ∧
    ∀ point, ¬Allowed point → snapshot.2 point=bg point := by
  have counts:=scanner_counts label
  have stackBounds:=valid_stack bg bound current valid
  refine ⟨counts.1,counts.2,?_,?_,?_⟩
  · have clock:=ScannerClock.clock_bound (scanner label) current.var current.stk (mass bg+bound) stackBounds
    calc
      ScannerStatement.clock (scanner label) current.var current.stk ≤
          2*ScannerClock.actions (scanner label)*(mass bg+bound+AuxWorkspace.pushes (scanner label)+1) := clock
      _ ≤ 2*3*(mass bg+bound+2+1) := Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 counts.1) (by omega)
      _ = 6*(mass bg+bound+3) := by ring
  · intro point
    exact (AuxWorkspace.node_bound (scanner label) current.var current.stk (mass bg+bound)
      stackBounds snapshot node point).trans (Nat.add_le_add_left counts.2 (mass bg+bound))
  · intro point outside
    exact (PSTRWordVM.StackIso.nodes_frame Allowed (scanner label) (scanner_writes label)
      current.var current.stk point outside snapshot node).trans (valid.2 point outside)

/-- Actual scanner lowering charge, with one dispatch per source state. -/
def charge {Λ σ : Type*} (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (trace : List (TM2.Cfg Alphabet Λ σ)) : Nat :=
  (trace.map (fun current => match current.l with
    | none => 0
    | some label => ScannerStatement.clock (machine label) current.var current.stk+1)).sum

theorem charge_le {Λ σ : Type*} (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (trace : List (TM2.Cfg Alphabet Λ σ)) (budget : Nat)
    (bounded : ∀ current∈trace, ∀ label, current.l=some label →
      ScannerStatement.clock (machine label) current.var current.stk+1≤budget) :
    charge machine trace≤budget*trace.length := by
  induction trace with
  | nil => simp [charge]
  | cons head tail ih =>
    have rest:=ih (fun current member => bounded current (List.mem_cons_of_mem _ member))
    have first : (match head.l with
      | none => 0
      | some label => ScannerStatement.clock (machine label) head.var head.stk+1)≤budget := by
      cases active : head.l with
      | none => simp
      | some label => exact bounded head List.mem_cons_self label active
    simp only [charge,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one] at rest ⊢
    omega

theorem scanner_clock (bg : Stack → List Bool) (bound : Nat) (current : ScanState)
    (valid : Valid bg bound current) (label : ScanLabel) :
    ScannerStatement.clock (scanner label) current.var current.stk≤6*(mass bg+bound+3) := by
  have snapshot:=AuxWorkspace.endpoint_mem (scanner label) current.var current.stk
  exact (scanner_resources bg bound current valid label _ snapshot).2.2.1

theorem actual_resume_trace (bg : Stack → List Bool) (mem : Store)
    (bits old : List Bool) (k : Nat) :
    ∃ trace final,
      trace.head?=some (state bg .clear mem bits old (unary k) []) ∧
      trace.IsChain (fun a b => TM2.step scanner a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤6*(old.length+k+bits.length+1) ∧ Outcome bg bits k final ∧
      (∀ current∈trace, Valid bg (old.length+k+bits.length+1) current) ∧
      (∀ current∈trace.dropLast, ∃ label, current.l=some label ∧ Proper label) ∧
      charge scanner trace≤
        (6*(mass bg+(old.length+k+bits.length+1)+3)+1)*(6*(old.length+k+bits.length+1)) := by
  obtain ⟨steps,final,run,time,outcome⟩:=actual_resume bg mem bits old k
  obtain ⟨trace,head,chain,last,length,bounds,interior⟩:=run.actual
  have time' : trace.length≤6*(old.length+k+bits.length+1) := by omega
  refine ⟨trace,final,head,chain,last,time',outcome,bounds,interior,?_⟩
  apply (charge_le scanner trace _ (fun current member label _ =>
    Nat.add_le_add_right (scanner_clock bg _ current (bounds current member) label) 1)).trans
  exact Nat.mul_le_mul_left _ time'
end RootB236.ControllerCandidate
