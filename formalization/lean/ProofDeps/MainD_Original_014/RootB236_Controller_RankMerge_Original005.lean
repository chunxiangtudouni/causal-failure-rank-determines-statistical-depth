module
public import RootB236_Controller_RankMerge_Resources004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankMerge
open Turing RootB23.GenericRank PaperProofs.Structure
variable {C : Type*}
local instance rankMergeENatOrder : LinearOrder ℕ∞ := instLinearOrderENat
local instance rankMergeENatTop : Top ℕ∞ := instOrderTopENat.toTop
local instance rankMergeENatDecEq : DecidableEq ℕ∞ := instLinearOrderENat.toDecidableEq

theorem rankBound_sup {A : Type*} (depth : Nat) (items : Finset A) (rank : A → ℕ∞)
    (bounded : ∀ item∈items,RankBound depth (rank item)) : RankBound depth (items.sup rank) := by
  apply Finset.sup_induction (rankBound_zero depth)
  · intro first firstBound later laterBound
    exact rankBound_max firstBound laterBound
  · exact bounded
/-- Finite rank bounds follow from the unchanged recurrence, including empty sup0 and terminal top. -/
theorem generic_rank_bound (q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    RankBound stages.length (genericRank stages remaining) := by
  induction stages generalizing remaining with
  | nil => exact Or.inl rfl
  | cons eligible later ih =>
    exact rankBound_min_succ (ih remaining)
      (rankBound_sup later.length (eligible∩remaining) (fun tool => genericRank later (remaining.erase tool))
        (fun tool _ => ih (remaining.erase tool)))

theorem rankCode_min (limit : Nat) (r s : ℕ∞) (hr : RankBound limit r) (hs : RankBound limit s) :
    rankCode limit (min r s)=min (rankCode limit r) (rankCode limit s) := by
  by_cases order : r≤s
  · have codes : rankCode limit r≤rankCode limit s := by
      apply Nat.le_of_not_gt
      intro reversed
      exact (not_lt_of_ge order) ((RankCompare.rankCode_lt_iff limit s r hs hr).mp reversed)
    rw [min_eq_left order,min_eq_left codes]
  · have reverse : s≤r := le_of_not_ge order
    have codes : rankCode limit s≤rankCode limit r := by
      apply Nat.le_of_not_gt
      intro reversed
      exact (not_lt_of_ge reverse) ((RankCompare.rankCode_lt_iff limit r s hr hs).mp reversed)
    rw [min_eq_right reverse,min_eq_right codes]

/-- Strict structural depth prevents a reachable finite successor from becoming the top sentinel. -/
theorem rankCode_succ (limit depth : Nat) (rank : ℕ∞) (level : depth<limit) (bound : RankBound depth rank) :
    cappedSucc (limit+1) (rankCode limit rank)=rankCode limit (1+rank) := by
  by_cases infinite : rank=⊤
  · simp [rankCode,infinite,cappedSucc]
  · have finite:=ENat.toNat_le_of_le_natCast (bound.resolve_left infinite)
    have strict : rank.toNat<limit+1 := by omega
    have addition : (1:ℕ∞)+rank≠⊤ := by
      intro same
      rcases ENat.add_eq_top.mp same with impossible | same
      · exact ENat.one_ne_top impossible
      · exact infinite same
    simp only [rankCode,ite_eq_right infinite,ite_eq_right addition]
    rw [cappedSucc,ite_eq_left strict,ENat.toNat_add ENat.one_ne_top infinite,ENat.toNat_one]
    omega

theorem finite_successor_below_sentinel (limit depth : Nat) (rank : ℕ∞) (level : depth<limit)
    (bound : RankBound depth rank) (finite : rank≠⊤) :
    cappedSucc (limit+1) (rankCode limit rank)≤limit ∧ cappedSucc (limit+1) (rankCode limit rank)≠limit+1 := by
  have small:=ENat.toNat_le_of_le_natCast (bound.resolve_left finite)
  have strict : rank.toNat<limit+1 := by omega
  simp only [rankCode,ite_eq_right finite,cappedSucc,ite_eq_left strict]
  omega

theorem successor_bound (limit depth : Nat) (rank : ℕ∞) (level : depth<limit) (bound : RankBound depth rank) :
    RankBound limit (1+rank) := by
  have bumped:=rankBound_min_succ (good:=(⊤:ℕ∞)) (bad:=rank) (Or.inl rfl) bound
  have small : RankBound (depth+1) (1+rank) := by simpa only [min_eq_right (le_top : (1:ℕ∞)+rank≤⊤)] using bumped
  exact small.mono (by omega)

theorem rankCode_merge (limit depth : Nat) (good bad : ℕ∞) (level : depth<limit)
    (goodBound : RankBound depth good) (badBound : RankBound depth bad) :
    merged (limit+1) (rankCode limit bad) (rankCode limit good)=rankCode limit (min good (1+bad)) := by
  rw [merged,rankCode_succ limit depth bad level badBound]
  rw [←rankCode_min limit (1+bad) good (successor_bound limit depth bad level badBound) (goodBound.mono (by omega))]
  rw [min_comm]

theorem Facts.original_value {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {trace : List (State C)} {final : State C}
    (limit depth : Nat) (good bad : ℕ∞) (level : depth<limit)
    (goodBound : RankBound depth good) (badBound : RankBound depth bad)
    (facts : Facts caller bg context ha hb ord (limit+1) (rankCode limit bad) (rankCode limit good) trace final) :
    final.stk 9=unary (rankCode limit (min good (1+bad))) ∧
      decodeRank limit (final.stk 9).length=min good (1+bad) := by
  have code : final.stk 9=unary (merged (limit+1) (rankCode limit bad) (rankCode limit good)) := by
    rw [facts.contents.2];rfl
  rw [rankCode_merge limit depth good bad level goodBound badBound] at code
  refine ⟨code,?_⟩
  rw [code]
  simp only [unary,RankCompare.unary,List.length_replicate]
  exact (rank_code_correct limit _ ((rankBound_min_succ goodBound badBound).mono (by omega))).1

noncomputable def childSup (q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) : ℕ∞ :=
  (eligible∩remaining).sup (fun tool => genericRank later (remaining.erase tool))
theorem original_scan_sup (q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) :
    bestRank (scan (fun tool => genericRank later (remaining.erase tool)) (genericRankCandidates q eligible remaining) none)=
      childSup q eligible later remaining := by
  rw [scan_rank,bestRank,zero_max,candidates_toFinset]
  rfl

theorem Facts.original_cons {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {trace : List (State C)} {final : State C}
    (limit q : Nat) (eligible : Finset (Fin q)) (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (level : (eligible::later).length≤limit)
    (facts : Facts caller bg context ha hb ord (limit+1) (rankCode limit (childSup q eligible later remaining))
      (rankCode limit (genericRank later remaining)) trace final) :
    final.stk 9=unary (rankCode limit (genericRank (eligible::later) remaining)) ∧
      decodeRank limit (final.stk 9).length=genericRank (eligible::later) remaining := by
  have depth : later.length<limit := by simp only [List.length_cons] at level;omega
  exact facts.original_value limit later.length (genericRank later remaining) (childSup q eligible later remaining) depth
    (generic_rank_bound q later remaining)
    (rankBound_sup later.length (eligible∩remaining) (fun tool => genericRank later (remaining.erase tool))
      (fun tool _ => generic_rank_bound q later (remaining.erase tool)))

/-- The original DFS scan-nil transition supplies its strict depth and child bounds itself. -/
theorem Facts.original_scan_nil {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {trace : List (State C)} {final : State C}
    (limit q : Nat) (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) (good : ℕ∞)
    (best : Best q) (stack : List (Frame q))
    (valid : WellFormed limit (⟨.scan later remaining [] good best,stack⟩ : RootB23.GenericRank.State q))
    (facts : Facts caller bg context ha hb ord (limit+1) (rankCode limit (bestRank best)) (rankCode limit good) trace final) :
    final.stk 9=unary (rankCode limit (min good (1+bestRank best))) ∧
      decodeRank limit (final.stk 9).length=min good (1+bestRank best) ∧
      RootB23.GenericRank.next (⟨.scan later remaining [] good best,stack⟩ : RootB23.GenericRank.State q)=
        some ⟨.answer (min good (1+bestRank best)) (bestTool best),stack⟩ := by
  have control:=valid.2
  change later.length+1≤expected limit stack ∧ [].length≤q ∧
    RankBound later.length good ∧ RankBound later.length (bestRank best) at control
  have outer:=expected_le stack valid.1
  have depth : later.length<limit := by omega
  have output:=facts.original_value limit later.length good (bestRank best) depth control.2.2.1 control.2.2.2
  exact ⟨output.1,output.2,rfl⟩

theorem Facts.outputs {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit a b : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb ord limit a b trace final) :
    final.l=some done ∧ final.stk 9=unary (merged limit a b) ∧ final.stk 10=unary b ∧
      final.stk 2=unary limit ∧ final.stk 7=[] ∧ final.stk 12=[] := by
  rw [facts.contents.2]
  exact ⟨facts.contents.1,rfl,rfl,rfl,rfl,rfl⟩

theorem Facts.top_stays_top {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb : Bool} {ord : Ordering} {limit : Nat} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb ord (limit+1) (limit+1) (limit+1) trace final) :
    final.stk 9=unary (limit+1) ∧ decodeRank limit (final.stk 9).length=⊤ := by
  have value : merged (limit+1) (limit+1) (limit+1)=limit+1 := by simp [merged,cappedSucc]
  have output:=facts.outputs.2.1
  rw [value] at output
  refine ⟨output,?_⟩
  rw [output]
  simp only [unary,RankCompare.unary,List.length_replicate,decodeRank,ite_true]
end RootB236.Controller.RankMerge
