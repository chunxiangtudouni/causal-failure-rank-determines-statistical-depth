module
public import Structure.RootB23_GenericRank_Cost_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.GenericRank

/-- RCC imports a noncomputable complete lattice. Finite comparisons use
the original computable ENat linear order, never choice-based suprema. -/
local instance finiteENatOrder : LinearOrder ℕ∞ := instLinearOrderENat
local instance finiteENatMin : Min ℕ∞ := instLinearOrderENat.toMin
local instance finiteENatTop : Top ℕ∞ := instOrderTopENat.toTop

inductive Frame (q : ℕ) where
  | good (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) (tools : List (Fin q))
  | bad (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
      (tools : List (Fin q)) (good : ℕ∞) (best : Best q) (tool : Fin q)

inductive Control (q : ℕ) where
  | call (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
  | answer (rank : ℕ∞) (pick : Option (Fin q))
  | scan (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
      (tools : List (Fin q)) (good : ℕ∞) (best : Best q)

structure State (q : ℕ) where
  control : Control q
  stack : List (Frame q)

/-- Explicit deterministic finite-data transitions. In particular next
never calls evaluate, genericRank, errorRank, or a semantic safety oracle.
List/Finset and scalar operations are exposed finite macros, not Bool ISA. -/
def next {q : ℕ} (state : State q) : Option (State q) :=
  match state.control,state.stack with
  | .call [] _,stack => some ⟨.answer ⊤ none,stack⟩
  | .call (eligible::later) remaining,stack =>
      some ⟨.call later remaining,
        .good later remaining (PaperProofs.Structure.genericRankCandidates q eligible remaining)::stack⟩
  | .answer _ _,[] => none
  | .answer rank _,.good later remaining tools::stack =>
      some ⟨.scan later remaining tools rank none,stack⟩
  | .answer rank _,.bad later remaining tools good best tool::stack =>
      some ⟨.scan later remaining tools good (update best tool rank),stack⟩
  | .scan _ _ [] good best,stack =>
      some ⟨.answer (min good (1+bestRank best)) (bestTool best),stack⟩
  | .scan later remaining (tool::tools) good best,stack =>
      some ⟨.call later (remaining.erase tool),.bad later remaining tools good best tool::stack⟩

/-- Finite genuine next-step path, with a bound on EVERY actual stack. -/
inductive Run {q : ℕ} (limit : ℕ) : State q → State q → ℕ → Prop where
  | refl {state : State q} (bounded : state.stack.length≤limit) : Run limit state state 0
  | step {before later after : State q} {steps : ℕ}
      (bounded : before.stack.length≤limit) (move : next before=some later)
      (rest : Run limit later after steps) : Run limit before after (steps+1)

theorem Run.weaken {q small large : ℕ} {before after : State q} {steps : ℕ}
    (run : Run small before after steps) (bound : small≤large) : Run large before after steps := by
  induction run with
  | refl bounded => exact .refl (bounded.trans bound)
  | step bounded move rest ih => exact .step (bounded.trans bound) move ih

theorem Run.append {q limit : ℕ} {before middle after : State q} {early later : ℕ}
    (first : Run limit before middle early) (last : Run limit middle after later) :
    Run limit before after (early+later) := by
  induction first with
  | refl bounded => simpa only [Nat.zero_add] using last
  | step bounded move rest ih =>
    rw [Nat.add_right_comm]
    exact Run.step bounded move (ih last)

theorem Run.single {q limit : ℕ} (before after : State q)
    (front : before.stack.length≤limit) (last : after.stack.length≤limit)
    (move : next before=some after) : Run limit before after 1 :=
  .step front move (.refl last)

def drive {q : ℕ} : ℕ → State q → State q
  | 0,state => state
  | count+1,state => drive count ((next state).getD state)

theorem Run.drive {q limit : ℕ} {before after : State q} {steps : ℕ}
    (run : Run limit before after steps) : drive steps before=after := by
  induction run with
  | refl bounded => rfl
  | @step before later after count bounded move rest ih =>
    change RootB23.GenericRank.drive count ((next before).getD before)=after
    rw [move]
    exact ih

theorem scan_run (q : ℕ) (later : List (Finset (Fin q)))
    (recursive : ∀ (remaining : Finset (Fin q)) (stack : List (Frame q)), ∃ steps,
      Run (stack.length+later.length) ⟨.call later remaining,stack⟩
        ⟨.answer (evaluate q later remaining).rank (evaluate q later remaining).pick,stack⟩ steps ∧
      steps+2=3*(evaluate q later remaining).nodes)
    (remaining : Finset (Fin q)) (tools : List (Fin q)) (good : ℕ∞) (best : Best q)
    (stack : List (Frame q)) :
    ∃ steps, Run (stack.length+later.length+1) ⟨.scan later remaining tools good best,stack⟩
      ⟨.answer (min good (1+bestRank (scan (fun tool => (evaluate q later (remaining.erase tool)).rank) tools best)))
        (bestTool (scan (fun tool => (evaluate q later (remaining.erase tool)).rank) tools best)),stack⟩ steps ∧
      steps=1+3*(tools.map (fun tool => (evaluate q later (remaining.erase tool)).nodes)).sum := by
  induction tools generalizing best with
  | nil =>
    refine ⟨1,Run.single _ _ (by dsimp;omega) (by dsimp;omega) rfl,?_⟩
    simp only [List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero]
  | cons tool tools ih =>
    obtain ⟨childSteps,child,childCost⟩:=recursive (remaining.erase tool)
      (Frame.bad later remaining tools good best tool::stack)
    have childBound : (Frame.bad later remaining tools good best tool::stack).length+later.length=
        stack.length+later.length+1 := by dsimp;omega
    rw [childBound] at child
    obtain ⟨tailSteps,tail,tailCost⟩:=ih (update best tool (evaluate q later (remaining.erase tool)).rank)
    have enter : Run (stack.length+later.length+1)
        ⟨.scan later remaining (tool::tools) good best,stack⟩
        ⟨.call later (remaining.erase tool),Frame.bad later remaining tools good best tool::stack⟩ 1 :=
      Run.single _ _ (by dsimp;omega) (by dsimp;omega) rfl
    have returned : Run (stack.length+later.length+1)
        ⟨.answer (evaluate q later (remaining.erase tool)).rank (evaluate q later (remaining.erase tool)).pick,
          Frame.bad later remaining tools good best tool::stack⟩
        ⟨.scan later remaining tools good (update best tool (evaluate q later (remaining.erase tool)).rank),stack⟩ 1 :=
      Run.single _ _ (by dsimp;omega) (by dsimp;omega) rfl
    refine ⟨1+childSteps+1+tailSteps,?_,?_⟩
    · exact ((enter.append child).append returned).append tail
    · simp only [List.map_cons,List.sum_cons,Nat.mul_add]
      omega

/-- A real terminating DFS path. Three finite macro transitions per
recursive node, minus two; actual stack height never exceeds suffix depth. -/
theorem evaluate_run (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (stack : List (Frame q)) :
    ∃ steps, Run (stack.length+stages.length) ⟨.call stages remaining,stack⟩
      ⟨.answer (evaluate q stages remaining).rank (evaluate q stages remaining).pick,stack⟩ steps ∧
      steps+2=3*(evaluate q stages remaining).nodes := by
  induction stages generalizing remaining stack with
  | nil =>
    refine ⟨1,Run.single _ _ (by simp) (by simp) rfl,?_⟩
    rfl
  | cons eligible later ih =>
    let tools:=PaperProofs.Structure.genericRankCandidates q eligible remaining
    obtain ⟨goodSteps,goodRun,goodCost⟩:=ih remaining (Frame.good later remaining tools::stack)
    have goodBound : (Frame.good later remaining tools::stack).length+later.length=
        stack.length+(eligible::later).length := by dsimp;omega
    rw [goodBound] at goodRun
    obtain ⟨scanSteps,scanning,scanCost⟩:=scan_run q later ih remaining tools
      (evaluate q later remaining).rank none stack
    have scanBound : stack.length+later.length+1=stack.length+(eligible::later).length := by
      simp only [List.length_cons];omega
    rw [scanBound] at scanning
    have enter : Run (stack.length+(eligible::later).length) ⟨.call (eligible::later) remaining,stack⟩
        ⟨.call later remaining,Frame.good later remaining tools::stack⟩ 1 :=
      Run.single _ _ (by dsimp;omega) (by dsimp;omega) rfl
    have returned : Run (stack.length+(eligible::later).length)
        ⟨.answer (evaluate q later remaining).rank (evaluate q later remaining).pick,
          Frame.good later remaining tools::stack⟩
        ⟨.scan later remaining tools (evaluate q later remaining).rank none,stack⟩ 1 :=
      Run.single _ _ (by dsimp;omega) (by dsimp;omega) rfl
    refine ⟨1+goodSteps+1+scanSteps,?_,?_⟩
    · simpa only [evaluate,scanChildren_formula] using ((enter.append goodRun).append returned).append scanning
    · rw [evaluate_nodes_cons]
      change 1+goodSteps+1+scanSteps+2=3*(1+(evaluate q later remaining).nodes+
        (tools.map (fun tool => (evaluate q later (remaining.erase tool)).nodes)).sum)
      rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
      omega

theorem dfs_actual (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    ∃ steps final, Run stages.length ⟨.call stages remaining,[]⟩ final steps ∧
      drive steps ⟨.call stages remaining,[]⟩=final ∧ next final=none ∧
      final.control=.answer (PaperProofs.Structure.genericRank stages remaining)
        (match stages with
        | [] => none
        | eligible::later => PaperProofs.Structure.pickGenericMaxRankTool q eligible later remaining) ∧
      steps≤3*structuralFactor stages.length q := by
  obtain ⟨steps,run,cost⟩:=evaluate_run q stages remaining []
  simp only [List.length_nil,Nat.zero_add] at run
  refine ⟨steps,⟨.answer (evaluate q stages remaining).rank (evaluate q stages remaining).pick,[]⟩,
    run,run.drive,rfl,?_,?_⟩
  · change Control.answer (evaluate q stages remaining).rank (evaluate q stages remaining).pick=_
    rw [(evaluate_exact q stages remaining).1,(evaluate_exact q stages remaining).2]
    rfl
  · have nodes:=Nat.mul_le_mul_left 3 (evaluate_nodes_one_factor q stages remaining)
    omega

end RootB23.GenericRank
