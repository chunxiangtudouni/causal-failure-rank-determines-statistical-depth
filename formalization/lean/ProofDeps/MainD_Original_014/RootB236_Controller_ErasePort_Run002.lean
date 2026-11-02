module
public import RootB236_Controller_ErasePort_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ErasePort
open Turing
variable {C : Type*}

def state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (mask count parked : List Bool) : State C :=
  ⟨some point,memory,Erase.cells background mask count parked⟩
def actualTrace (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix : List Bool) : List (State C) :=
  (Erase.actualTrace background context present saved skipped head suffix []).map configuration

theorem chain_configuration (caller : Statement C) (trace : List (Erase.State C))
    (chain : trace.IsChain (fun a b => TM2.step Erase.program a=some b)) :
    (trace.map configuration).IsChain (fun a b => TM2.step (program caller) a=some b) :=
  List.isChain_map_of_isChain configuration (fun a b edge => edge_configuration caller a b edge) chain

theorem no_early_none (trace : List (Erase.State C))
    (chain : trace.IsChain (fun a b => TM2.step Erase.program a=some b)) :
    ∀ current∈trace.dropLast, current.l≠none := by
  induction trace with
  | nil => simp
  | cons first rest ih =>
    cases rest with
    | nil => simp
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with same | member
      · subst current
        intro halted
        cases first with
        | mk point memory slots =>
          change point=none at halted
          subst point
          cases edge
      · exact ih later current member

theorem no_early_port (trace : List (Erase.State C))
    (chain : trace.IsChain (fun a b => TM2.step Erase.program a=some b)) :
    ∀ current∈(trace.map configuration).dropLast, current.l≠some 2 := by
  rw [←List.map_dropLast]
  intro current member reached
  obtain ⟨old,present,same⟩:=List.mem_map.mp member
  subst current
  exact no_early_none trace chain old present ((port_iff old).mp reached)

def WorkBound (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  ∃ old : Erase.State C, Erase.WorkBound background context bound old ∧ current=configuration old

structure Facts (caller : Statement C) (background : Stack → List Bool) (context : C)
    (present saved : Bool) (skipped : List Bool) (head : Bool) (suffix : List Bool)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (state background 0 (context,present,saved)
    (skipped++head::suffix) (List.replicate skipped.length true) [])
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  contents : final=state background 2 (context,false,false)
    (skipped++false::suffix) (List.replicate skipped.length true) []
  active : final.l=some 2
  time : trace.length=2*skipped.length+3
  no_early : ∀ current∈trace.dropLast,current.l≠some 2
  boundary : ∀ current∈trace,WorkBound background context (2*skipped.length+suffix.length+1) current

theorem actual_facts (caller : Statement C) (background : Stack → List Bool) (context : C)
    (present saved : Bool) (skipped : List Bool) (head : Bool) (suffix : List Bool) :
    Facts caller background context present saved skipped head suffix
      (actualTrace background context present saved skipped head suffix)
      (state background 2 (context,false,false) (skipped++false::suffix)
        (List.replicate skipped.length true) []) := by
  have facts:=Erase.actual_facts background context present saved skipped head suffix
  refine ⟨?_,chain_configuration caller _ facts.chain,?_,rfl,rfl,?_,no_early_port _ facts.chain,?_⟩
  · simp only [actualTrace,List.head?_map,facts.first,Option.map_some]
    rfl
  · simp only [actualTrace,List.getLast?_map,facts.last,Option.map_some]
    rfl
  · simpa only [actualTrace,List.length_map] using facts.time
  · intro current member
    obtain ⟨old,present,same⟩:=List.mem_map.mp member
    exact ⟨old,facts.boundary old present,same.symm⟩

theorem Facts.context {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace) : current.var.1=context := by
  obtain ⟨old,within,rfl⟩:=facts.boundary current member
  exact Erase.work_context _ _ _ _ within
theorem Facts.frame {caller : Statement C} {background : Stack → List Bool} {context : C}
    {present saved : Bool} {skipped : List Bool} {head : Bool} {suffix : List Bool}
    {trace : List (State C)} {final : State C}
    (facts : Facts caller background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace) (point : Stack)
    (notMask : point≠4) (notCount : point≠5) (notParked : point≠7) :
    current.stk point=background point := by
  obtain ⟨old,within,rfl⟩:=facts.boundary current member
  exact Erase.work_frame _ _ _ _ within point notMask notCount notParked
end RootB236.Controller.ErasePort
