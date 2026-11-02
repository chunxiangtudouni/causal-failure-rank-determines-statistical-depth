module
public import RootB236_Controller_BestUpdate_Original005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing RootB23.GenericRank PaperProofs.Common.Native.PSTRWordBool
open scoped BigOperators
variable {C : Type*}

theorem initial_mass_measured (bg : Stack → List Bool) (context : C) (ha hb flag : Bool)
    (ord : Ordering) (a b tool : Nat) (best tail : List Bool) :
    initialMass bg a b tool best flag tail=
      ∑ slot : Stack,((state boot (context,ha,hb,ord) (bank bg a b tool best flag tail)).stk slot).length := rfl

theorem Facts.occupied {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final)
    (current : State C) (member : current∈trace) :
    (∑ slot : Stack,(current.stk slot).length)≤4112*scale bg a b tool best flag tail := by
  calc
    (∑ slot : Stack,(current.stk slot).length)≤∑ _slot : Stack,257*scale bg a b tool best flag tail :=
      Finset.sum_le_sum (fun slot _ => (facts.boundaries current member).2.1 slot)
    _=4112*scale bg a b tool best flag tail := by simp;omega

theorem Facts.internal_occupied {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final)
    (current : State C) (member : current∈trace.dropLast) (point : Label) (active : current.l=some point)
    (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program caller point) current.var current.stk) :
    (∑ slot : Stack,(node.2 slot).length)≤4368*scale bg a b tool best flag tail := by
  calc
    (∑ slot : Stack,(node.2 slot).length)≤∑ _slot : Stack,273*scale bg a b tool best flag tail :=
      Finset.sum_le_sum (fun slot _ => ((facts.internal current member point active).1 node inside).2.1 slot)
    _=4368*scale bg a b tool best flag tail := by simp;omega

namespace Public
/-- One actual path exposes all semantic and resource projections. Return is ACTIVE and unexecuted. -/
theorem actual (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (best tail : List Bool) :
    ∃ trace final,Facts caller bg context ha hb flag ord a b tool best tail trace final ∧
      (∀ current∈trace,current.var.1=context ∧
        (∀ slot,(current.stk slot).length≤257*scale bg a b tool best flag tail) ∧
        ∀ slot,¬Work slot → current.stk slot=bg slot) ∧
      traceClockSum caller trace≤144000*(scale bg a b tool best flag tail)^2 ∧
      trace.length+traceClockSum caller trace≤144016*(scale bg a b tool best flag tail)^2 := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb flag ord a b tool best tail
  exact ⟨trace,final,facts,facts.boundaries,facts.clock_sum,facts.charged⟩

theorem fixed_source (C : Type*) [Fintype C] (caller : Statement C) :
    ∃ (source : Label → Statement C) (support : Finset Label),source=program caller ∧
      support.card=13 ∧ TM2.Supports source support ∧ Fintype.card (Store C)=Fintype.card C*12 ∧
      ∀ (bg : Stack → List Bool) (context : C) (ha hb flag : Bool) (ord : Ordering)
        (a b tool : Nat) (best tail : List Bool),
        ∃ trace final,Facts caller bg context ha hb flag ord a b tool best tail trace final ∧
          trace.length+traceClockSum caller trace≤144016*(scale bg a b tool best flag tail)^2 := by
  refine ⟨program caller,Finset.univ,rfl,by decide,supports caller,?_,?_⟩
  · change Fintype.card (C×(Bool×Bool×Ordering))=Fintype.card C*12
    simp only [Fintype.card_prod,Fintype.card_bool]
    rw [show Fintype.card Ordering=3 by decide]
  · intro bg context ha hb flag ord a b tool best tail
    obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb flag ord a b tool best tail
    exact ⟨trace,final,facts,facts.charged⟩

/-- Original update and unchanged finite-rank semantics, on exactly the operational witness. -/
theorem original_update {q : Nat} (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a : Nat) (oldTool tail : List Bool)
    (limit : Nat) (best : Best q) (tool : Fin q) (rank : ℕ∞)
    (entry : EntryRepresentation limit best flag a oldTool) (bounded : RankBound limit rank) :
    ∃ trace final,Facts caller bg context ha hb flag ord a (rankCode limit rank) tool.val oldTool tail trace final ∧
      BestRepresentation limit tail (RootB23.GenericRank.update best tool rank) final.stk ∧
      trace.length+traceClockSum caller trace≤144016*(scale bg a (rankCode limit rank) tool.val oldTool flag tail)^2 := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb flag ord a (rankCode limit rank) tool.val oldTool tail
  exact ⟨trace,final,facts,(facts.original_update limit best tool rank entry bounded).2,facts.charged⟩

/-- First candidate of score0/tool0 is selected, even with arbitrary stale best-tool bits. -/
theorem first_zero (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a : Nat) (oldTool tail : List Bool) :
    ∃ trace final,Facts caller bg context ha hb false ord a 0 0 oldTool tail trace final ∧
      final.l=some done ∧ final.stk 13=true::tail ∧ final.stk 9=[] ∧ final.stk 14=[] := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb false ord a 0 0 oldTool tail
  refine ⟨trace,final,facts,facts.contents.1,?_⟩
  rw [facts.contents.2,resultBank_update bg a 0 0 oldTool tail false (Or.inl rfl)]
  exact ⟨rfl,rfl,rfl⟩

theorem equal_top_first (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (limit tool old : Nat) (tail : List Bool) :
    ∃ trace final,Facts caller bg context ha hb true ord (limit+1) (limit+1) tool (unary old) tail trace final ∧
      final.stk 14=unary old ∧ final.stk 9=unary (limit+1) := by
  obtain ⟨trace,final,facts⟩:=actual_facts caller bg context ha hb true ord (limit+1) (limit+1) tool (unary old) tail
  exact ⟨trace,final,facts,facts.equal_top_keeps_first⟩
end Public
end RootB236.Controller.BestUpdate
