module
public import RootB236_Controller_DFSDriver_Return008

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*} {q : Nat}

/-- Proof-side interpretation of the three actual Best data fields. -/
abbrev CodeBest (q : Nat) := Option (Fin q × Nat)
def bestCode : CodeBest q → Nat | none => 0 | some (_,rank) => rank
def toolCode : CodeBest q → List Bool | none => [] | some (tool,_) => unary tool.val
def hasCode (best : CodeBest q) : Bool := best.isSome
def updateCode (best : CodeBest q) (tool : Fin q) (rank : Nat) : CodeBest q :=
  match best with
  | none => some (tool,rank)
  | some (old,previous) => if previous<rank then some (tool,rank) else some (old,previous)
def scanCode (score : Fin q → Nat) (tools : List (Fin q)) (best : CodeBest q) : CodeBest q :=
  tools.foldl (fun best tool => updateCode best tool (score tool)) best

def dataBank (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool) : Stack → List Bool :=
  fun slot => if slot=2 then unary limit else if slot=9 then unary (bestCode best) else if slot=10 then unary skip else
    if slot=13 then hasCode best::tail else if slot=14 then toolCode best else if slot=15 then [] else bg slot

def scanBank (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool k : Nat) : Stack → List Bool :=
  SelectErase.bank (dataBank bg limit skip best tail) bits current (unary tool) (unary k) [] parent.reverse (unary parent.length) []

def bestInput (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool k rank : Nat) : Stack → List Bool :=
  Function.update (scanBank bg limit skip best tail bits current parent tool k) 15 (unary rank)

/-- The physical10/15 permutation frames the saved skip rank. -/
theorem best_input (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool k rank : Nat) :
    StackIso.slots badRoles
      (BestUpdate.bank (StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool k rank))
        (bestCode best) rank tool (toolCode best) (hasCode best) tail)=
      bestInput bg limit skip best tail bits current parent tool k rank := by
  funext slot;fin_cases slot <;> rfl

/-- Strictly better ranks update; equality keeps the first physical tool. -/
theorem best_result (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool : Fin q) (k rank : Nat) :
    Function.update (StackIso.slots badRoles
      (BestUpdate.resultBank (StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool.val k rank))
        (bestCode best) rank tool.val (toolCode best) (hasCode best) tail)) 15 []=
      scanBank bg limit skip (updateCode best tool rank) tail bits current parent tool.val k := by
  cases best with
  | none =>
    simp only [bestCode,toolCode,hasCode,Option.isSome_none]
    rw [BestUpdate.resultBank_update _ _ _ _ _ _ _ (Or.inl rfl)]
    funext slot;fin_cases slot <;> rfl
  | some pair =>
    rcases pair with ⟨old,previous⟩
    simp only [bestCode,toolCode,hasCode,Option.isSome_some]
    by_cases strict : previous<rank
    · rw [BestUpdate.resultBank_update _ _ _ _ _ _ _ (Or.inr strict)]
      simp only [updateCode,ite_eq_left strict]
      funext slot;fin_cases slot <;> rfl
    · have keep : ¬BestUpdate.selected true previous rank := by
        intro selected;rcases selected with impossible | better
        · cases impossible
        · exact strict better
      rw [BestUpdate.resultBank_keep _ _ _ _ _ _ _ keep]
      simp only [updateCode,ite_eq_right strict]
      funext slot;fin_cases slot <;> rfl

/-- A complete bad-return prefix, including physical clear15 before the actual continuation. -/
theorem update_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip : Nat) (best : CodeBest q) (tail : List Bool) (bits current parent : List Bool)
    (tool : Fin q) (k rank : Nat) :
    ∃ steps finalMemory,Path good bad pop finish
      (state returnedBad memory (bestInput bg limit skip best tail bits current parent tool.val k rank))
      (state (.resume .clear) finalMemory (scanBank bg limit skip (updateCode best tool rank) tail bits current parent tool.val k)) steps ∧
      finalMemory.1=memory.1 ∧
      steps≤16*(BestUpdate.scale (StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool.val k rank))
        (bestCode best) rank tool.val (toolCode best) (hasCode best) tail)+(rank+1) := by
  let input:=bestInput bg limit skip best tail bits current parent tool.val k rank
  obtain ⟨trace,final,facts,actual⟩:=bad_to_resume good bad pop finish (StackIso.slots badRoles input)
    memory.1 memory.2.1 memory.2.2.1 (hasCode best) memory.2.2.2 (bestCode best) rank tool.val (toolCode best) tail
  change Path good bad pop finish
    (state returnedBad memory (StackIso.slots badRoles
      (BestUpdate.bank (StackIso.slots badRoles input) (bestCode best) rank tool.val (toolCode best) (hasCode best) tail)))
    (state (.resume .clear) _ _) _ at actual
  dsimp only [input] at actual
  rw [best_input] at actual
  rw [facts.contents.2,best_result] at actual
  refine ⟨_,_,actual,?_,?_⟩
  · exact (facts.boundaries final (List.mem_of_getLast? facts.last)).1
  · have time:=facts.time;dsimp only [input] at time;omega

/-- No unary conversion of raw input is performed by these interpretations. -/
structure CodeAnswer (q : Nat) where
  rank : Nat
  pick : Option (Fin q)

def evaluateCode (q limit : Nat) : List (Finset (Fin q)) → Finset (Fin q) → CodeAnswer q
  | [],_ => ⟨limit,none⟩
  | eligible::later,remaining =>
    let good:=evaluateCode q limit later remaining
    let best:=scanCode (fun tool => (evaluateCode q limit later (remaining.erase tool)).rank)
      (genericRankCandidates q eligible remaining) none
    ⟨RankMerge.merged limit (bestCode best) good.rank,best.map Prod.fst⟩

end RootB236.Controller.DFSDriver
