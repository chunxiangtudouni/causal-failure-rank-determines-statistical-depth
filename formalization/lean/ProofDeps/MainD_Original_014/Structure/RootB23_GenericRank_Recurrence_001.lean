module
public import PaperProofs.Structure.RankEvaluator

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
@[expose] public section

namespace RootB23.GenericRank
open PaperProofs.Structure

abbrev Best (q : ℕ) := Option (Fin q × ℕ∞)

def bestTool {q : ℕ} : Best q → Option (Fin q)
  | none => none
  | some (tool, _) => some tool

def bestRank {q : ℕ} : Best q → ℕ∞
  | none => 0
  | some (_, rank) => rank

theorem zero_max (rank : ℕ∞) : max 0 rank=rank :=
  max_eq_right (a := (0 : ℕ∞)) (b := rank) (by exact zero_le)

theorem max_zero (rank : ℕ∞) : max rank 0=rank :=
  max_eq_left (a := rank) (b := (0 : ℕ∞)) (by exact zero_le)

/-- Strict improvement only: equal ranks keep the FIRST finRange tool. -/
def update {q : ℕ} (best : Best q) (tool : Fin q) (rank : ℕ∞) : Best q :=
  match best with
  | none => some (tool, rank)
  | some (old, previous) =>
      if previous < rank then some (tool, rank) else some (old, previous)

def Scored {q : ℕ} (score : Fin q → ℕ∞) (best : Best q) : Prop :=
  ∀ tool rank, best=some (tool,rank) → rank=score tool

theorem scored_none {q : ℕ} (score : Fin q → ℕ∞) : Scored score none := by
  intro tool rank impossible
  cases impossible

theorem scored_update {q : ℕ} (score : Fin q → ℕ∞) (best : Best q)
    (scored : Scored score best) (tool : Fin q) :
    Scored score (update best tool (score tool)) := by
  intro chosen rank equal
  cases best with
  | none =>
    simp only [update,Option.some.injEq,Prod.mk.injEq] at equal
    rcases equal with ⟨rfl,rfl⟩
    rfl
  | some pair =>
    rcases pair with ⟨old, previous⟩
    by_cases better : previous < score tool
    · simp only [update, better, ite_true, Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl,rfl⟩
      rfl
    · simp only [update, better, ite_false, Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl,rfl⟩
      exact scored old previous rfl

theorem bestRank_update {q : ℕ} (best : Best q) (tool : Fin q) (rank : ℕ∞) :
    bestRank (update best tool rank)=max (bestRank best) rank := by
  cases best with
  | none => exact (zero_max rank).symm
  | some pair =>
    rcases pair with ⟨old, previous⟩
    by_cases better : previous<rank
    · simp only [update,better,ite_true,bestRank,max_eq_right (le_of_lt better)]
    · simp only [update,better,ite_false,bestRank,max_eq_left (le_of_not_gt better)]

theorem bestTool_update {q : ℕ} (score : Fin q → ℕ∞) (best : Best q)
    (scored : Scored score best) (tool : Fin q) :
    bestTool (update best tool (score tool))=
      List.argAux (fun new old => score old < score new) (bestTool best) tool := by
  cases best with
  | none => rfl
  | some pair =>
    rcases pair with ⟨old, previous⟩
    have same := scored old previous rfl
    simp only [update,bestTool,List.argAux,same]
    split_ifs <;> rfl

def scan {q : ℕ} (score : Fin q → ℕ∞) (tools : List (Fin q)) (best : Best q) : Best q :=
  tools.foldl (fun accumulator tool => update accumulator tool (score tool)) best

theorem scan_tool {q : ℕ} (score : Fin q → ℕ∞) (tools : List (Fin q))
    (best : Best q) (scored : Scored score best) :
    bestTool (scan score tools best)=
      tools.foldl (List.argAux (fun new old => score old < score new)) (bestTool best) := by
  induction tools generalizing best with
  | nil => rfl
  | cons tool later ih =>
    rw [scan,List.foldl_cons,←scan,ih _ (scored_update score best scored tool),
      bestTool_update score best scored tool]
    rfl

theorem scan_rank {q : ℕ} (score : Fin q → ℕ∞) (tools : List (Fin q)) (best : Best q) :
    bestRank (scan score tools best)=max (bestRank best) (tools.toFinset.sup score) := by
  induction tools generalizing best with
  | nil => simp only [scan,List.foldl_nil,List.toFinset_nil,Finset.sup_empty,
      bot_eq_zero,max_zero]
  | cons tool later ih =>
    rw [scan,List.foldl_cons,←scan,ih,bestRank_update,List.toFinset_cons,Finset.sup_insert]
    exact max_assoc _ _ _

theorem scan_argmax {q : ℕ} (score : Fin q → ℕ∞) (tools : List (Fin q)) :
    bestTool (scan score tools none)=List.argmax score tools :=
  scan_tool score tools none (scored_none score)

theorem candidates_toFinset (q : ℕ) (eligible remaining : Finset (Fin q)) :
    (genericRankCandidates q eligible remaining).toFinset=eligible∩remaining := by
  ext tool
  simp only [List.mem_toFinset,mem_genericRankCandidates]

theorem candidates_length (q : ℕ) (eligible remaining : Finset (Fin q)) :
    (genericRankCandidates q eligible remaining).length≤q := by
  simpa only [genericRankCandidates,List.length_finRange] using
    List.length_filter_le (fun tool => decide (tool∈eligible∩remaining)) (List.finRange q)

structure Answer (q : ℕ) where
  rank : ℕ∞
  pick : Option (Fin q)
  nodes : ℕ

/-- One child is evaluated once and immediately folded into a constant
size accumulator. This is NOT an array/table of all child answers. -/
def scanChildren {q : ℕ} (child : Fin q → Answer q) (tools : List (Fin q))
    (accumulator : Best q × ℕ) : Best q × ℕ :=
  tools.foldl (fun accumulator tool =>
    let reply := child tool
    (update accumulator.1 tool reply.rank,accumulator.2+reply.nodes)) accumulator

theorem scanChildren_formula {q : ℕ} (child : Fin q → Answer q) (tools : List (Fin q))
    (best : Best q) (nodes : ℕ) :
    scanChildren child tools (best,nodes)=
      (scan (fun tool => (child tool).rank) tools best,
        nodes+(tools.map (fun tool => (child tool).nodes)).sum) := by
  induction tools generalizing best nodes with
  | nil => simp only [scanChildren,scan,List.foldl_nil,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons tool later ih =>
    simp only [scanChildren,List.foldl_cons]
    change scanChildren child later
      (update best tool (child tool).rank,nodes+(child tool).nodes)=_
    rw [ih]
    simp only [scan,List.foldl_cons,List.map_cons,List.sum_cons,Nat.add_assoc]

/-- Finite recursive procedure: good child first, then exact finRange
candidates in order. No errorRank/genericRank value is an input or a call. -/
def evaluate (q : ℕ) : List (Finset (Fin q)) → Finset (Fin q) → Answer q
  | [], _ => ⟨⊤,none,1⟩
  | eligible::later, remaining =>
      let good := evaluate q later remaining
      let accumulated := scanChildren
        (fun tool => evaluate q later (remaining.erase tool))
        (genericRankCandidates q eligible remaining) (none,1+good.nodes)
      ⟨min good.rank (1+bestRank accumulated.1),bestTool accumulated.1,accumulated.2⟩

theorem evaluate_exact (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluate q stages remaining).rank=genericRank stages remaining ∧
    (evaluate q stages remaining).pick=
      match stages with
      | [] => none
      | eligible::later => pickGenericMaxRankTool q eligible later remaining := by
  induction stages generalizing remaining with
  | nil => exact ⟨rfl,rfl⟩
  | cons eligible later ih =>
    simp only [evaluate,scanChildren_formula]
    have children : (fun tool => (evaluate q later (remaining.erase tool)).rank)=
        (fun tool => genericRank later (remaining.erase tool)) :=
      funext (fun tool => (ih (remaining.erase tool)).1)
    rw [children]
    constructor
    · rw [scan_rank,bestRank,zero_max,candidates_toFinset,(ih remaining).1]
      rfl
    · exact scan_argmax _ _

theorem evaluate_nodes_cons (q : ℕ) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluate q (eligible::later) remaining).nodes=1+(evaluate q later remaining).nodes+
      ((genericRankCandidates q eligible remaining).map
        (fun tool => (evaluate q later (remaining.erase tool)).nodes)).sum := by
  simp only [evaluate,scanChildren_formula]

end RootB23.GenericRank
