module
public import RootB236_Controller_ErasePort_Resources003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ErasePort
open Turing
variable {C : Type*}
namespace Public

theorem actual (caller : Statement C) (background : Stack → List Bool) (context : C)
    (present saved : Bool) (skipped : List Bool) (head : Bool) (suffix : List Bool) :
    ∃ trace final,Facts caller background context present saved skipped head suffix trace final ∧
      traceClockSum caller trace≤12*(scale background skipped suffix)^2 ∧
      trace.length+traceClockSum caller trace≤14*(scale background skipped suffix)^2 := by
  have facts:=actual_facts caller background context present saved skipped head suffix
  exact ⟨_,_,facts,facts.clock_sum,facts.charged⟩

/-- Fixed source/support/finite store precede all runtime mask and counter data. -/
theorem fixed_source (C : Type*) [Fintype C] (caller : Statement C) :
    ∃ (source : Label → Statement C) (support : Finset Label),
      source=program caller ∧ support.card=3 ∧ TM2.Supports source support ∧
      Fintype.card (Store C)=Fintype.card C*4 ∧
      ∀ (background : Stack → List Bool) (context : C) (present saved : Bool)
        (skipped : List Bool) (head : Bool) (suffix : List Bool),
        ∃ trace final,Facts caller background context present saved skipped head suffix trace final ∧
          traceClockSum caller trace≤12*(scale background skipped suffix)^2 ∧
          trace.length+traceClockSum caller trace≤14*(scale background skipped suffix)^2 := by
  refine ⟨program caller,Finset.univ,rfl,by decide,supports caller,?_,actual caller⟩
  change Fintype.card (C×Bool×Bool)=Fintype.card C*4
  simp only [Fintype.card_prod,Fintype.card_bool]

/-- The restore body is also an actual entry1-to-ACTIVE2 callee, same old witness. -/
theorem restore_active (caller : Statement C) (background : Stack → List Bool) (context : C)
    (present saved : Bool) (parked mask count : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (state background 1 (context,present,saved) mask count parked) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧ trace.getLast?=some final ∧
      final=state background 2 (context,false,false) (parked.reverse++mask)
        (List.replicate parked.length true++count) [] ∧
      final.l=some 2 ∧ trace.length=parked.length+2 ∧
      (∀ current∈trace.dropLast,current.l≠some 2) ∧
      ∀ current∈trace,WorkBound background context (2*parked.length+mask.length+count.length) current := by
  let old:=Erase.restoreTrace background context present saved parked mask count
  let final:=state background 2 (context,false,false) (parked.reverse++mask)
    (List.replicate parked.length true++count) []
  have chain:=Erase.restore_chain background context present saved parked mask count
  refine ⟨old.map configuration,final,?_,chain_configuration caller old chain,?_,rfl,rfl,?_,no_early_port old chain,?_⟩
  · simp only [List.head?_map,old,Erase.restore_head,Option.map_some]
    rfl
  · simp only [List.getLast?_map,old,Erase.restore_last,Option.map_some]
    rfl
  · simpa only [List.length_map,old] using Erase.restore_length background context present saved parked mask count
  · intro current member
    obtain ⟨original,inOld,same⟩:=List.mem_map.mp member
    exact ⟨original,Erase.restore_bound background context present saved parked mask count original inOld,same.symm⟩

example (statement : Erase.Statement C) (memory : Store C) (slots : Stack → List Bool) :
    TM2.stepAux (body statement) memory slots=configuration (TM2.stepAux statement memory slots) :=
  stepAux_configuration statement memory slots
example (caller : Statement C) (trace : List (Erase.State C))
    (chain : trace.IsChain (fun a b => TM2.step Erase.program a=some b)) :
    traceClockSum caller (trace.map configuration)=Erase.traceClockSum trace :=
  clock_sum_configuration caller trace chain
end Public
end RootB236.Controller.ErasePort
