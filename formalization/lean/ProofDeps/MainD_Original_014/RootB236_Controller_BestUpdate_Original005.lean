module
public import RootB236_Controller_BestUpdate_Resources004
public import RootB236_Controller_RankCompare_RankCode004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing RootB23.GenericRank
variable {C : Type*}
local instance bestUpdateENatOrder : LinearOrder ℕ∞ := instLinearOrderENat
local instance bestUpdateENatTop : Top ℕ∞ := instOrderTopENat.toTop
local instance bestUpdateENatDecEq : DecidableEq ℕ∞ := instLinearOrderENat.toDecidableEq

/-- Internal bounded-current-rank representation. None ignores the stale old data. -/
def EntryRepresentation {q : Nat} (limit : Nat) (best : Best q)
    (flag : Bool) (oldCode : Nat) (oldTool : List Bool) : Prop :=
  match best with
  | none => flag=false
  | some (old,rank) => flag=true ∧ oldCode=rankCode limit rank ∧
      oldTool=unary old.val ∧ RankBound limit rank
/-- Three physical fields of the caller's Best frame; no decoder is claimed here. -/
def BestRepresentation {q : Nat} (limit : Nat) (tail : List Bool) (best : Best q)
    (slots : Stack → List Bool) : Prop :=
  match best with
  | none => slots 13=false::tail
  | some (tool,rank) => slots 13=true::tail ∧ slots 9=unary (rankCode limit rank) ∧ slots 14=unary tool.val

theorem result_original {q : Nat} (limit : Nat) (bg : Stack → List Bool) (best : Best q)
    (flag : Bool) (oldCode : Nat) (oldTool tail : List Bool) (tool : Fin q) (rank : ℕ∞)
    (entry : EntryRepresentation limit best flag oldCode oldTool) (bounded : RankBound limit rank) :
    BestRepresentation limit tail (RootB23.GenericRank.update best tool rank)
      (resultBank bg oldCode (rankCode limit rank) tool.val oldTool flag tail) := by
  cases best with
  | none =>
    change flag=false at entry
    subst flag
    rw [resultBank_update bg oldCode (rankCode limit rank) tool.val oldTool tail false (Or.inl rfl)]
    exact ⟨rfl,rfl,rfl⟩
  | some best =>
    rcases best with ⟨old,previous⟩
    change flag=true ∧ oldCode=rankCode limit previous ∧ oldTool=unary old.val ∧ RankBound limit previous at entry
    obtain ⟨rfl,rfl,rfl,oldBound⟩:=entry
    by_cases strict : previous<rank
    · have codes : rankCode limit previous<rankCode limit rank :=
        (RankCompare.rankCode_lt_iff limit previous rank oldBound bounded).mpr strict
      change BestRepresentation limit tail
        (if previous<rank then some (tool,rank) else some (old,previous)) _
      rw [ite_eq_left strict,resultBank_update bg (rankCode limit previous) (rankCode limit rank)
        tool.val (unary old.val) tail true (Or.inr codes)]
      exact ⟨rfl,rfl,rfl⟩
    · have keep : ¬selected true (rankCode limit previous) (rankCode limit rank) := by
        intro choice;rcases choice with impossible | codes
        · cases impossible
        · exact strict ((RankCompare.rankCode_lt_iff limit previous rank oldBound bounded).mp codes)
      change BestRepresentation limit tail
        (if previous<rank then some (tool,rank) else some (old,previous)) _
      rw [ite_eq_right strict,resultBank_keep bg (rankCode limit previous) (rankCode limit rank)
        tool.val (unary old.val) tail true keep]
      exact ⟨rfl,rfl,rfl⟩

theorem Facts.original_update {q : Nat} {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a : Nat} {oldTool tail : List Bool} {trace : List (State C)} {final : State C}
    (limit : Nat) (best : Best q) (tool : Fin q) (rank : ℕ∞)
    (entry : EntryRepresentation limit best flag a oldTool) (bounded : RankBound limit rank)
    (facts : Facts caller bg context ha hb flag ord a (rankCode limit rank) tool.val oldTool tail trace final) :
    final.l=some done ∧ BestRepresentation limit tail (RootB23.GenericRank.update best tool rank) final.stk := by
  refine ⟨facts.contents.1,?_⟩
  rw [facts.contents.2]
  exact result_original limit bg best flag a oldTool tail tool rank entry bounded

theorem Facts.outputs {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final) :
    final.l=some done ∧ final.stk 13=true::tail ∧ final.stk 10=unary b ∧ final.stk 5=unary tool ∧
      final.stk 7=[] ∧ final.stk 12=[] ∧
      final.stk 9=unary (if selected flag a b then b else a) ∧
      final.stk 14=(if selected flag a b then unary tool else best) := by
  rw [facts.contents.2]
  exact ⟨facts.contents.1,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem Facts.equal_keeps_first {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {a tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb true ord a a tool best tail trace final) : final.stk 14=best ∧ final.stk 9=unary a := by
  have keep : ¬selected true a a := by
    intro choice;rcases choice with impossible | strict
    · cases impossible
    · omega
  rw [facts.contents.2,resultBank_keep bg a a tool best tail true keep]
  exact ⟨rfl,rfl⟩
/-- Top has code N+1; equality cannot replace the first Fin-range tool. -/
theorem Facts.equal_top_keeps_first {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit tool old : Nat} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb true ord (limit+1) (limit+1) tool (unary old) tail trace final) :
    final.stk 14=unary old ∧ final.stk 9=unary (limit+1) := facts.equal_keeps_first

/-- No Fin0 candidate is manufactured by the typed bridge. -/
theorem no_zero_tool (tool : Fin 0) : False := Fin.elim0 tool
end RootB236.Controller.BestUpdate
