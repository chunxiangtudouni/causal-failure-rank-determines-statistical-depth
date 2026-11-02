module
public import RootB236_Controller_RankCompare_Resources003
public import Structure.RootB23_GenericRank_FiniteData_005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankCompare
open Turing RootB23.GenericRank
variable {C : Type*}
local instance rankCompareENatOrder : LinearOrder ℕ∞ := instLinearOrderENat
local instance rankCompareENatTop : Top ℕ∞ := instOrderTopENat.toTop
local instance rankCompareENatDecEq : DecidableEq ℕ∞ := instLinearOrderENat.toDecidableEq

/-- Original finite rank coding, including top=N+1. This is proof-only. -/
theorem rankCode_lt_iff (limit : Nat) (r s : ℕ∞) (hr : RankBound limit r) (hs : RankBound limit s) :
    rankCode limit r<rankCode limit s ↔ r<s := by
  by_cases rTop : r=⊤
  · by_cases sTop : s=⊤
    · simp only [rankCode,rTop,sTop,ite_true,lt_self_iff_false]
    · have bound:=ENat.toNat_le_of_le_natCast (hs.resolve_left sTop)
      have impossible : ¬r<s := by rw [rTop];exact not_lt_of_ge le_top
      simp only [rankCode,ite_eq_left rTop,ite_eq_right sTop]
      constructor
      · intro small;exact False.elim (by omega)
      · intro small;exact False.elim (impossible small)
  · by_cases sTop : s=⊤
    · have bound:=ENat.toNat_le_of_le_natCast (hr.resolve_left rTop)
      have strict : r<s := by rw [sTop];exact lt_top_iff_ne_top.mpr rTop
      simp only [rankCode,ite_eq_right rTop,ite_eq_left sTop]
      exact ⟨fun _ => strict,fun _ => by omega⟩
    · calc
        rankCode limit r<rankCode limit s ↔ r.toNat<s.toNat := by
          simp only [rankCode,ite_eq_right rTop,ite_eq_right sTop]
        _ ↔ (r.toNat : ℕ∞)<(s.toNat : ℕ∞) := ENat.natCast_lt_natCast.symm
        _ ↔ r<s := by rw [ENat.natCast_toNat rTop,ENat.natCast_toNat sTop]

theorem rankCode_eq_iff (limit : Nat) (r s : ℕ∞) (hr : RankBound limit r) (hs : RankBound limit s) :
    rankCode limit r=rankCode limit s ↔ r=s := by
  constructor
  · intro same
    exact (rank_code_correct limit r hr).1.symm.trans
      ((congrArg (decodeRank limit) same).trans (rank_code_correct limit s hs).1)
  · intro same;exact congrArg (rankCode limit) same

/-- No new encoding: unary counters represent the unchanged bounded original codes. -/
theorem Facts.rank_ports {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit : Nat} {r s : ℕ∞} {trace : List (State C)} {final : State C}
    (hr : RankBound limit r) (hs : RankBound limit s)
    (facts : Facts lt eq gt bg context ha hb ord (rankCode limit r) (rankCode limit s) trace final) :
    (final.l=some 3 ↔ r<s) ∧ (final.l=some 4 ↔ r=s) ∧ (final.l=some 5 ↔ s<r) :=
  ⟨facts.ports.1.trans (rankCode_lt_iff limit r s hr hs),
    facts.ports.2.1.trans (rankCode_eq_iff limit r s hr hs),
    facts.ports.2.2.trans (rankCode_lt_iff limit s r hs hr)⟩

theorem Facts.rank_time {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit : Nat} {r s : ℕ∞} {trace : List (State C)} {final : State C}
    (hr : RankBound limit r) (hs : RankBound limit s)
    (facts : Facts lt eq gt bg context ha hb ord (rankCode limit r) (rankCode limit s) trace final) :
    trace.length≤4*limit+8 := by
  have left:=(rank_code_correct limit r hr).2
  have right:=(rank_code_correct limit s hs).2
  have time:=facts.time
  omega
theorem Facts.rank_workspace {lt eq gt : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit : Nat} {r s : ℕ∞} {trace : List (State C)} {final : State C}
    (hr : RankBound limit r) (hs : RankBound limit s)
    (facts : Facts lt eq gt bg context ha hb ord (rankCode limit r) (rankCode limit s) trace final)
    (current : State C) (member : current∈trace) (point : Stack) :
    (current.stk point).length≤backgroundMass bg+2*(limit+1) := by
  have left:=(rank_code_correct limit r hr).2
  have right:=(rank_code_correct limit s hs).2
  have within:=work_uniform bg context _ current (facts.boundary current member) point
  omega
end RootB236.Controller.RankCompare
