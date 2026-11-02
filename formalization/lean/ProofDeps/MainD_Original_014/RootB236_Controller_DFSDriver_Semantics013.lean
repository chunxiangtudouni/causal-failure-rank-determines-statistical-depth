module
public import RootB236_Controller_DFSDriver_Data009

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open RootB23.GenericRank PaperProofs.Structure
variable {q : Nat}
local instance driverENatOrder : LinearOrder ℕ∞ := instLinearOrderENat
local instance driverENatTop : Top ℕ∞ := instOrderTopENat.toTop
local instance driverENatDecEq : DecidableEq ℕ∞ := instLinearOrderENat.toDecidableEq

/-- Logical decoding of bounded current-rank fields; never part of the source ROM. -/
noncomputable def encodeBest (limit : Nat) (best : Best q) : CodeBest q :=
  best.map (fun pair => (pair.1,rankCode limit pair.2))

theorem encoded_rank (limit : Nat) (best : Best q) : bestCode (encodeBest limit best)=rankCode limit (bestRank best) := by
  cases best with
  | none => simp [encodeBest,bestCode,bestRank,rankCode]
  | some pair => rfl

theorem encoded_tool (limit : Nat) (best : Best q) : (encodeBest limit best).map Prod.fst=bestTool best := by
  cases best <;> rfl

theorem update_encode (limit : Nat) (best : Best q) (tool : Fin q) (rank : ℕ∞)
    (oldBound : RankBound limit (bestRank best)) (newBound : RankBound limit rank) :
    updateCode (encodeBest limit best) tool (rankCode limit rank)=encodeBest limit (update best tool rank) := by
  cases best with
  | none => rfl
  | some pair =>
    rcases pair with ⟨old,previous⟩
    have order:=RankCompare.rankCode_lt_iff limit previous rank oldBound newBound
    simp only [encodeBest,Option.map_some,updateCode,update]
    split_ifs with hc hr hr
    · rfl
    · exact False.elim (hr (order.mp hc))
    · exact False.elim (hc (order.mpr hr))
    · rfl

theorem scan_encode (limit : Nat) (score : Fin q → ℕ∞) (tools : List (Fin q)) (best : Best q)
    (bounded : ∀ tool,RankBound limit (score tool)) (oldBound : RankBound limit (bestRank best)) :
    scanCode (fun tool => rankCode limit (score tool)) tools (encodeBest limit best)=
      encodeBest limit (scan score tools best) := by
  induction tools generalizing best with
  | nil => rfl
  | cons tool later ih =>
    change scanCode _ later (updateCode (encodeBest limit best) tool (rankCode limit (score tool)))=_
    rw [update_encode limit best tool (score tool) oldBound (bounded tool)]
    apply ih
    rw [bestRank_update]
    exact rankBound_max oldBound (bounded tool)

theorem code_scan_bound (limit : Nat) (score : Fin q → Nat) (tools : List (Fin q)) (best : CodeBest q)
    (bounded : ∀ tool,score tool≤limit) (oldBound : bestCode best≤limit) :
    bestCode (scanCode score tools best)≤limit := by
  induction tools generalizing best with
  | nil => exact oldBound
  | cons tool later ih =>
    change bestCode (scanCode score later (updateCode best tool (score tool)))≤limit
    apply ih
    cases best with
    | none => exact bounded tool
    | some pair =>
      rcases pair with ⟨old,previous⟩
      simp only [updateCode]
      split_ifs
      · exact bounded tool
      · exact oldBound

theorem code_rank_bound (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluateCode q limit stages remaining).rank≤limit := by
  induction stages generalizing remaining with
  | nil => exact Nat.le_refl limit
  | cons eligible later ih =>
    exact (Nat.min_le_right _ _).trans (ih remaining)

/-- The capped code recurrence equals the unchanged generic rank and FIRST maximizer. -/
theorem evaluate_code_original (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (depth : stages.length≤limit) :
    (evaluateCode q (limit+1) stages remaining).rank=rankCode limit (genericRank stages remaining) ∧
    (evaluateCode q (limit+1) stages remaining).pick=
      match stages with
      | [] => none
      | eligible::later => pickGenericMaxRankTool q eligible later remaining := by
  induction stages generalizing remaining with
  | nil => simp [evaluateCode,genericRank,rankCode]
  | cons eligible later ih =>
    have level : later.length<limit := by simp only [List.length_cons] at depth;omega
    have childBound : ∀ tool : Fin q,RankBound later.length (genericRank later (remaining.erase tool)) :=
      fun tool => RankMerge.generic_rank_bound q later (remaining.erase tool)
    have children : (fun tool => (evaluateCode q (limit+1) later (remaining.erase tool)).rank)=
        (fun tool => rankCode limit (genericRank later (remaining.erase tool))) :=
      funext (fun tool => (ih (remaining.erase tool) (by omega)).1)
    have good:=(ih remaining (by omega)).1
    let score:=fun tool => genericRank later (remaining.erase tool)
    let tools:=genericRankCandidates q eligible remaining
    let best:=scan score tools none
    have encoded:=scan_encode limit score tools none
      (fun tool => (childBound tool).mono (by omega)) (rankBound_zero limit)
    have sup : bestRank best=RankMerge.childSup q eligible later remaining := RankMerge.original_scan_sup q eligible later remaining
    change (evaluateCode q (limit+1) (eligible::later) remaining).rank=_ ∧ _
    simp only [evaluateCode]
    rw [children,good]
    change RankMerge.merged (limit+1) (bestCode (scanCode (fun tool => rankCode limit (score tool)) tools none))
      (rankCode limit (genericRank later remaining))=_ ∧
      (scanCode (fun tool => rankCode limit (score tool)) tools none).map Prod.fst=_
    have empty : encodeBest limit (none : Best q)=none := rfl
    rw [←empty,encoded,encoded_rank,encoded_tool]
    constructor
    · rw [sup]
      exact RankMerge.rankCode_merge limit later.length (genericRank later remaining)
        (RankMerge.childSup q eligible later remaining) level (RankMerge.generic_rank_bound q later remaining)
        (RankMerge.rankBound_sup later.length (eligible∩remaining) score (fun tool _ => childBound tool))
    · exact scan_argmax score tools
end RootB236.Controller.DFSDriver
