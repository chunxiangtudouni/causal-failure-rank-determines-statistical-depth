module
public import Structure.RootB23_GenericRank_Bounded_006

/-! Deterministic high-level queries execute the existing explicit DFS next.
The returned counter counts actual nonterminal transitions. F is only an
already-proved fuel bound, never the definition of the measured counter. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Structure
open PaperProofs.Common.Native RationalControllerComputation
open RootB23.GenericRank

def execute {q : Nat} : Nat→Nat→State q→State q×Nat
  | 0,elapsed,state => (state,elapsed)
  | fuel+1,elapsed,state =>
      match next state with
      | none => (state,elapsed)
      | some later => execute fuel (elapsed+1) later

theorem execute_state {q : Nat} (fuel elapsed : Nat) (state : State q) :
    (execute fuel elapsed state).1=drive fuel state := by
  induction fuel generalizing elapsed state with
  | zero => rfl
  | succ fuel ih =>
      cases move : next state with
      | none =>
          simp only [execute,move]
          exact (drive_halted _ _ move).symm
      | some later =>
          simpa only [execute,drive,move,Option.getD_some] using ih (elapsed+1) later

theorem execute_count {q : Nat} (fuel elapsed : Nat) (state : State q) :
    elapsed≤(execute fuel elapsed state).2 ∧ (execute fuel elapsed state).2≤elapsed+fuel := by
  induction fuel generalizing elapsed state with
  | zero => simp only [execute,Nat.add_zero,le_refl,and_self]
  | succ fuel ih =>
      cases move : next state with
      | none => simp only [execute,move];omega
      | some later =>
          have bounded:=ih (elapsed+1) later
          simp only [execute,move]
          constructor <;> omega

structure RankReply (q : Nat) where
  rank : ℕ∞
  pick : Option (Fin q)
  transitions : Nat

def query (I : Instance) (stage : Nat) (remaining : Finset I.Tool) : RankReply I.toolCount :=
  let result:=execute (3*generalStructureFactor I) 0 ⟨.call (I.compatibility.drop stage) remaining,[]⟩
  match result.1.control with
  | .answer rank pick => ⟨rank,pick,result.2⟩
  | _ => ⟨⊤,none,result.2⟩

theorem query_spec (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    (query I stage remaining).rank=genericRank (I.compatibility.drop stage) remaining ∧
    (query I stage remaining).pick=(match I.compatibility.drop stage with
      | [] => none
      | eligible::later => pickGenericMaxRankTool I.toolCount eligible later remaining) ∧
    (query I stage remaining).transitions≤3*generalStructureFactor I := by
  obtain ⟨steps,final,_run,_steps,_actual,finished,_halted,correct,_width,_ranks⟩:=
    original_suffix_dfs I stage remaining
  have state:=(execute_state (3*generalStructureFactor I) 0
    (⟨.call (I.compatibility.drop stage) remaining,[]⟩ : State I.toolCount)).trans finished
  have control:=congrArg (fun state : State I.toolCount => state.control) state
  rw [correct] at control
  have count:=(execute_count (3*generalStructureFactor I) 0
    (⟨.call (I.compatibility.drop stage) remaining,[]⟩ : State I.toolCount)).2
  have shape : query I stage remaining=⟨genericRank (I.compatibility.drop stage) remaining,
      (match I.compatibility.drop stage with
        | [] => none
        | eligible::later => pickGenericMaxRankTool I.toolCount eligible later remaining),
      (execute (3*generalStructureFactor I) 0
        (⟨.call (I.compatibility.drop stage) remaining,[]⟩ : State I.toolCount)).2⟩ := by
    dsimp only [query]
    rw [control]
    rfl
  rw [shape]
  exact ⟨rfl,rfl,by simpa only [Nat.zero_add] using count⟩

def kind (I : Instance) (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) :
    Option PaperProofs.Statistics.ReferenceBudgetCase :=
  let remaining:=available\used
  let root:=query I stage.val remaining
  let bad:=match root.pick with
    | none => 0
    | some tool => (query I (stage.val+1) (remaining.erase tool)).rank
  referenceCaseOfRanks root.rank bad

theorem suffix_cons (I : Instance) (stage : I.Stage) :
    I.compatibility.drop stage.val=I.eligible stage::I.compatibility.drop (stage.val+1) := by
  exact List.drop_eq_getElem_cons stage.isLt

theorem query_pick (I : Instance) (stage : I.Stage) (remaining : Finset I.Tool) :
    (query I stage.val remaining).pick=
      pickGenericMaxRankTool I.toolCount (I.eligible stage) (I.compatibility.drop (stage.val+1)) remaining := by
  simpa only [suffix_cons] using (query_spec I stage.val remaining).2.1

theorem kind_eq (I : Instance) (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) :
    kind I available stage used=referenceAvailableRankCase I available stage used := by
  dsimp only [kind]
  unfold referenceAvailableRankCase referenceRankCase referenceBadRank referenceRankAt referenceRepairTool
  simp only [referenceRank_remaining,Finset.sdiff_insert]
  rw [query_pick I stage (available\used),(query_spec I stage.val (available\used)).1]
  cases picked : pickGenericMaxRankTool I.toolCount (I.eligible stage)
      (I.compatibility.drop (stage.val+1)) (available\used) with
  | none => rfl
  | some tool =>
      simp only [(query_spec I (stage.val+1) ((available\used).erase tool)).1]

end RootPaper.Reference
