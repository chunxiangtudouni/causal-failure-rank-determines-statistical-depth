module
public import RootB236_Controller_RankMerge_Original005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankMerge
open Turing RootB23.GenericRank PaperProofs.Structure PaperProofs.Common.Native.PSTRWordBool
open scoped BigOperators
variable {C : Type*}
theorem initial_mass_measured (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    initialMass bg limit a b=
      ∑ slot : Stack,((state entry (context,ha,hb,ord) (bank bg limit a b)).stk slot).length := rfl

theorem Facts.occupied {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb ord limit a b trace final)
    (current : State C) (member : current∈trace) :
    (∑ slot : Stack,(current.stk slot).length)≤4112*scale bg limit a b := by
  calc
    (∑ slot : Stack,(current.stk slot).length)≤∑ _slot : Stack,257*scale bg limit a b :=
      Finset.sum_le_sum (fun slot _ => (facts.boundaries current member).2.1 slot)
    _=4112*scale bg limit a b := by simp;omega

theorem Facts.internal_occupied {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb ord limit a b trace final)
    (current : State C) (member : current∈trace.dropLast) (point : Label) (active : current.l=some point)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program caller point) current.var current.stk) :
    (∑ slot : Stack,(node.2 slot).length)≤4368*scale bg limit a b := by
  calc
    (∑ slot : Stack,(node.2 slot).length)≤∑ _slot : Stack,273*scale bg limit a b :=
      Finset.sum_le_sum (fun slot _ => ((facts.internal current member point active).1 node inside).2.1 slot)
    _=4368*scale bg limit a b := by simp;omega

theorem cappedSucc_valid (limit a : Nat) (valid : a≤limit) :
    cappedSucc limit a=min (a+1) limit := by
  by_cases strict : a<limit
  · rw [cappedSucc,ite_eq_left strict,min_eq_left (by omega)]
  · rw [cappedSucc,ite_eq_right strict,min_eq_right (by omega)]
    omega

theorem Facts.valid_codes {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb ord limit a b trace final) (valid : a≤limit) :
    final.stk 9=unary (min (min (a+1) limit) b) := by
  have output:=facts.outputs.2.1
  rw [merged,cappedSucc_valid limit a valid] at output
  exact output

namespace Public

theorem actual (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ trace final,Facts caller bg context ha hb ord limit a b trace final ∧
      (∀ current∈trace,current.var.1=context ∧
        (∀ slot,(current.stk slot).length≤257*scale bg limit a b) ∧
        ∀ slot,¬Work slot → current.stk slot=bg slot) ∧
      traceClockSum caller trace≤144000*(scale bg limit a b)^2 ∧
      trace.length+traceClockSum caller trace≤144016*(scale bg limit a b)^2 := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord limit a b
  exact ⟨trace,final,facts,facts.boundaries,facts.clock_sum,facts.charged⟩

theorem fixed_source (C : Type*) [Fintype C] (caller : Statement C) :
    ∃ (source : Label → Statement C) (support : Finset Label),source=program caller ∧
      support.card=13 ∧ TM2.Supports source support ∧ Fintype.card (Store C)=Fintype.card C*12 ∧
      ∀ (bg : Stack → List Bool) (context : C) (ha hb : Bool) (ord : Ordering) (limit a b : Nat),
        ∃ trace final,Facts caller bg context ha hb ord limit a b trace final ∧
          trace.length+traceClockSum caller trace≤144016*(scale bg limit a b)^2 := by
  refine ⟨program caller,Finset.univ,rfl,by decide,supports caller,?_,?_⟩
  · change Fintype.card (C×(Bool×Bool×Ordering))=Fintype.card C*12
    simp only [Fintype.card_prod,Fintype.card_bool]
    rw [show Fintype.card Ordering=3 by decide]
  · intro bg context ha hb ord limit a b
    obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord limit a b
    exact ⟨trace,final,facts,facts.charged⟩

/-- All schedule nodes with the root's existing structural size bound. -/
theorem original_cons (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (level : (eligible::later).length≤limit) :
    ∃ trace final,Facts caller bg context ha hb ord (limit+1) (rankCode limit (childSup q eligible later remaining))
      (rankCode limit (genericRank later remaining)) trace final ∧
      final.stk 9=unary (rankCode limit (genericRank (eligible::later) remaining)) ∧
      decodeRank limit (final.stk 9).length=genericRank (eligible::later) remaining ∧
      trace.length+traceClockSum caller trace≤144016*
        (scale bg (limit+1) (rankCode limit (childSup q eligible later remaining))
          (rankCode limit (genericRank later remaining)))^2 := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord (limit+1)
    (rankCode limit (childSup q eligible later remaining)) (rankCode limit (genericRank later remaining))
  have output:=facts.original_cons limit q eligible later remaining level
  exact ⟨trace,final,facts,output.1,output.2,facts.charged⟩

/-- No extra rank-bound assumption: choose the schedule's actual node depth. -/
theorem original_node (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    ∃ trace final,Facts caller bg context ha hb ord (later.length+2)
      (rankCode (later.length+1) (childSup q eligible later remaining))
      (rankCode (later.length+1) (genericRank later remaining)) trace final ∧
      final.stk 9=unary (rankCode (later.length+1) (genericRank (eligible::later) remaining)) ∧
      decodeRank (later.length+1) (final.stk 9).length=genericRank (eligible::later) remaining := by
  obtain ⟨trace,final,facts,code,value,_charge⟩:=original_cons caller bg context ha hb ord (later.length+1) q eligible later remaining (by exact le_rfl)
  exact ⟨trace,final,facts,code,value⟩

/-- The unchanged original scan-nil state supplies all semantic premises internally. -/
theorem original_scan_nil (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit q : Nat) (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (good : ℕ∞) (best : Best q) (stack : List (Frame q))
    (valid : WellFormed limit (⟨.scan later remaining [] good best,stack⟩ : RootB23.GenericRank.State q)) :
    ∃ trace final,Facts caller bg context ha hb ord (limit+1) (rankCode limit (bestRank best)) (rankCode limit good) trace final ∧
      final.stk 9=unary (rankCode limit (min good (1+bestRank best))) ∧
      decodeRank limit (final.stk 9).length=min good (1+bestRank best) ∧
      RootB23.GenericRank.next (⟨.scan later remaining [] good best,stack⟩ : RootB23.GenericRank.State q)=
        some ⟨.answer (min good (1+bestRank best)) (bestTool best),stack⟩ := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord (limit+1) (rankCode limit (bestRank best)) (rankCode limit good)
  have output:=facts.original_scan_nil limit q later remaining good best stack valid
  exact ⟨trace,final,facts,output⟩

/-- Empty candidates supply the original sup0, with no positive-counter assumption. -/
theorem empty_candidates (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (level : (eligible::later).length≤limit) (empty : eligible∩remaining=∅) :
    ∃ trace final,Facts caller bg context ha hb ord (limit+1) 0 (rankCode limit (genericRank later remaining)) trace final ∧
      final.stk 9=unary (rankCode limit (genericRank (eligible::later) remaining)) ∧
      decodeRank limit (final.stk 9).length=genericRank (eligible::later) remaining := by
  obtain ⟨trace,final,facts,code,value,_charge⟩:=original_cons caller bg context ha hb ord limit q eligible later remaining level
  have zero : rankCode limit (childSup q eligible later remaining)=0 := by simp [childSup,empty,rankCode]
  rw [zero] at facts
  exact ⟨trace,final,facts,code,value⟩

theorem zero_counters (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool) (ord : Ordering) :
    ∃ trace final,Facts caller bg context ha hb ord 0 0 0 trace final ∧ final.stk 9=[] ∧ final.stk 10=[] ∧ final.stk 2=[] := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord 0 0 0
  refine ⟨trace,final,facts,?_,facts.outputs.2.2.1,facts.outputs.2.2.2.1⟩
  have output:=facts.outputs.2.1
  simpa only [merged,cappedSucc,Nat.lt_irrefl,ite_false,Nat.min_self,unary,RankCompare.unary,List.replicate_zero] using output

theorem top_boundary (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit : Nat) :
    ∃ trace final,Facts caller bg context ha hb ord (limit+1) (limit+1) (limit+1) trace final ∧
      final.stk 9=unary (limit+1) ∧ decodeRank limit (final.stk 9).length=⊤ := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb ord (limit+1) (limit+1) (limit+1)
  exact ⟨trace,final,facts,facts.top_stays_top⟩

/-- N=0 is terminal in the original recurrence; its unchanged top code is1. -/
theorem empty_schedule (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (q : Nat) (remaining : Finset (Fin q)) :
    ∃ trace final,Facts caller bg context ha hb ord 1 1 1 trace final ∧ final.stk 9=unary 1 ∧
      decodeRank 0 (final.stk 9).length=genericRank ([] : List (Finset (Fin q))) remaining := by
  obtain ⟨trace,final,facts,code,value⟩:=top_boundary caller bg context ha hb ord 0
  exact ⟨trace,final,facts,code,value⟩
end Public
end RootB236.Controller.RankMerge
