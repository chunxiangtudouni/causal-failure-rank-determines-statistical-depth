module
public import Structure.RootB236_Controller_Candidate_Bridge_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing
open PaperProofs.Common.Native
open PSTRWordBool PSTRWordVM

theorem statement_identity (body : Statement) : LabelMap.statement id body=body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact congrArg _ ih
  | branch _ _ _ iy ino => exact congrArg₂ _ iy ino
  | goto _ | halt => rfl
theorem configuration_identity (current : State) : LabelMap.configuration id current=current := by
  cases current with
  | mk label memory slots => cases label <;> rfl

/-- The same leaf path works with arbitrary FIXED active return-port code. -/
theorem actual_caller_splice (found empty : Statement) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => TM2.step source a=some b))
    (last : trace.getLast?=some final) (active : final.l≠none) :
    trace.IsChain (fun a b => TM2.step (program found empty) a=some b) := by
  have noFound:=no_early_halt_port source (.inr .found) rfl trace final chain last active
  have noEmpty:=no_early_halt_port source (.inr .empty) rfl trace final chain last active
  have mapped:=LabelMap.chain_configuration_on id source (program found empty) trace chain
    (by
      intro current member label atLabel
      rw [statement_identity]
      cases label with
      | inl _ => rfl
      | inr label =>
        cases label <;> first | rfl |
          exact False.elim (noFound current member atLabel) |
          exact False.elim (noEmpty current member atLabel))
  have same : (LabelMap.configuration id : State → State)=id := funext configuration_identity
  simpa only [same,List.map_id] using mapped

theorem context_node_bound {C : Type*} (context : C) (current : State) (bound : Nat)
    (bounded : ∀ point, (current.stk point).length≤bound) (label : Label)
    (snapshot : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=C×Store))
    (node : snapshot∈AuxWorkspace.nodes (withContext C label) (context,current.var) current.stk) :
    snapshot.1.1=context ∧ ∀ point, (snapshot.2 point).length≤bound+2 := by
  change snapshot∈AuxWorkspace.nodes (ContextLift.statement (source label)) (context,current.var) current.stk at node
  rw [ContextLift.nodes_configuration] at node
  obtain ⟨original,present,same⟩:=List.mem_map.mp node
  subst snapshot
  refine ⟨rfl,?_⟩
  intro point
  exact (AuxWorkspace.node_bound (source label) current.var current.stk bound bounded original present point).trans
    (by have pushes:=(source_counts label).2;omega)

/-- Separate continuation entry, including actual old5 cleanup and finite C transport. -/
theorem actual_resume_context {C : Type*} (context : C) (bg : Stack → List Bool)
    (mem : Store) (bits old : List Bool) (k : Nat) :
    ∃ (trace : List (TM2.Cfg Alphabet Label (C×Store))) (final : TM2.Cfg Alphabet Label (C×Store)),
      trace.head?=some (inContext context (scanEmbed (state bg .clear mem bits old (unary k) []))) ∧
      trace.IsChain (fun a b => TM2.step (withContext C) a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤6*(old.length+k+bits.length+1) ∧
      (∃ scanFinal, Outcome bg bits k scanFinal ∧ final=inContext context (scanEmbed scanFinal)) ∧
      (∀ current∈trace, current.var.1=context ∧
        (∀ point, (current.stk point).length≤mass bg+(old.length+k+bits.length+1)) ∧
        ∀ point, ¬Allowed point → current.stk point=bg point) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ∀ snapshot∈AuxWorkspace.nodes (withContext C label) current.var current.stk,
          snapshot.1.1=context ∧
          ∀ point, (snapshot.2 point).length≤mass bg+(old.length+k+bits.length+1)+2) ∧
      charge (withContext C) trace≤
        (10*(mass bg+(old.length+k+bits.length+1)+3)+1)*(6*(old.length+k+bits.length+1)) := by
  obtain ⟨base,scanFinal,head,chain,last,time,outcome,bounds,interior,_charge⟩:=
    actual_resume_trace bg mem bits old k
  have mapped:=LabelMap.actual_path_on scanLabels scanner source base _ _ head chain last
    (fun current member label atLabel => scan_agrees .halt .halt label
      (by obtain ⟨actualLabel,equal,proper⟩:=interior current member
          have same : label=actualLabel := Option.some.inj (atLabel.symm.trans equal)
          exact same ▸ proper))
  let global:=base.map scanEmbed
  have lifted:=ContextLift.actual_path source context global _ _ mapped.1 mapped.2.1 mapped.2.2.1
  refine ⟨global.map (inContext context),inContext context (scanEmbed scanFinal),
    lifted.1,lifted.2.1,lifted.2.2.1,?_,⟨scanFinal,outcome,rfl⟩,?_,?_,?_⟩
  · simpa only [global,List.length_map] using time
  · intro current member
    obtain ⟨mid,inGlobal,same⟩:=List.mem_map.mp member
    obtain ⟨original,inBase,midSame⟩:=List.mem_map.mp inGlobal
    subst current; subst mid
    exact ⟨rfl,valid_stack bg _ original (bounds original inBase),(bounds original inBase).2⟩
  · intro current member label _active snapshot node
    obtain ⟨mid,inGlobal,same⟩:=List.mem_map.mp member
    obtain ⟨original,inBase,midSame⟩:=List.mem_map.mp inGlobal
    subst current; subst mid
    exact context_node_bound context (scanEmbed original) _
      (valid_stack bg _ original (bounds original inBase)) label snapshot node
  · apply (charge_le (withContext C) _ _ ?_).trans
    · exact Nat.mul_le_mul_left _ (by simpa only [global,List.length_map] using time)
    · intro current member label _active
      obtain ⟨mid,inGlobal,same⟩:=List.mem_map.mp member
      obtain ⟨original,inBase,midSame⟩:=List.mem_map.mp inGlobal
      subst current; subst mid
      exact Nat.add_le_add_right (context_clock context (scanEmbed original) _
        (valid_stack bg _ original (bounds original inBase)) label) 1

/-- Repeated scan keeps uniform q bounds; old5 is physically consumed by clear. -/
theorem actual_resume_extent (bg : Stack → List Bool) (mem : Store)
    (bits old : List Bool) (k q : Nat) (extent : k+bits.length=q) (oldBound : old.length≤q) :
    ∃ (trace : List ScanState) (final : ScanState),
      trace.head?=some (state bg .clear mem bits old (unary k) []) ∧
      trace.IsChain (fun a b => TM2.step scanner a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤12*(q+1) ∧ Outcome bg bits k final ∧
      ∀ current∈trace, ∀ point, (current.stk point).length≤(bg point).length+(2*q+1) := by
  obtain ⟨trace,final,head,chain,last,time,outcome,bounds,_interior,_charge⟩:=actual_resume_trace bg mem bits old k
  refine ⟨trace,final,head,chain,last,by omega,outcome,?_⟩
  intro current member point
  have bounded:=(bounds current member).1 point
  omega
end RootB236.ControllerCandidate
