module
public import Structure.RootB23_GenericRank_Workspace_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
@[expose] public section
namespace RootB23.GenericRank

local instance codecENatOrder005 : LinearOrder ℕ∞ := instLinearOrderENat
local instance codecENatTop005 : Top ℕ∞ := instOrderTopENat.toTop
local instance codecENatDecEq005 : DecidableEq ℕ∞ := instLinearOrderENat.toDecidableEq

def rankCode (limit : ℕ) (rank : ℕ∞) : ℕ :=
  if rank=⊤ then limit+1 else rank.toNat

def decodeRank (limit code : ℕ) : ℕ∞ := if code=limit+1 then ⊤ else (code : ℕ∞)

theorem rank_code_correct (limit : ℕ) (rank : ℕ∞) (bound : RankBound limit rank) :
    decodeRank limit (rankCode limit rank)=rank ∧ rankCode limit rank≤limit+1 := by
  by_cases infinite : rank=⊤
  · simp only [rankCode,infinite,ite_true,decodeRank,ite_true,le_refl,and_self]
  · have finite : rank≤(limit : ℕ∞) := bound.resolve_left infinite
    have codeBound:=ENat.toNat_le_of_le_natCast finite
    have different : rank.toNat≠limit+1 := by omega
    constructor
    · simp only [rankCode,infinite,ite_false,decodeRank,different,ite_false]
      exact ENat.natCast_toNat infinite
    · simp only [rankCode,infinite,ite_false]
      omega

theorem rank_finite_representation (limit : ℕ) (rank : ℕ∞) (bound : RankBound limit rank) :
    ∃ code : Fin (limit+2), decodeRank limit code.val=rank := by
  have correct:=rank_code_correct limit rank bound
  exact ⟨⟨rankCode limit rank,by omega⟩,correct.1⟩

def frameRanks {q : ℕ} : Frame q → List ℕ∞
  | .good _ _ _ => []
  | .bad _ _ _ good best _ => [good,bestRank best]

def controlRanks {q : ℕ} : Control q → List ℕ∞
  | .call _ _ => []
  | .answer rank _ => [rank]
  | .scan _ _ _ good best => [good,bestRank best]

def stateRanks {q : ℕ} (state : State q) : List ℕ∞ :=
  controlRanks state.control++state.stack.flatMap frameRanks

theorem frame_ranks_bound {q root : ℕ} (frame : Frame q)
    (valid : FrameValid frame) (depth : frameDepth frame≤root) :
    ∀ rank∈frameRanks frame, RankBound root rank := by
  cases frame with
  | good => intro rank impossible;cases impossible
  | bad later remaining tools good best tool =>
    intro rank member
    simp only [frameRanks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact valid.2.1.mono depth
    · exact valid.2.2.mono depth

theorem state_ranks_bound {q root : ℕ} (state : State q) (valid : WellFormed root state) :
    ∀ rank∈stateRanks state, RankBound root rank := by
  have expectation:=expected_le state.stack valid.1
  have frames:=frame_bounds state.stack valid.1
  intro rank member
  rcases List.mem_append.mp member with control|stack
  · have controlValid:=valid.2
    cases equation : state.control with
    | call stages remaining =>
      rw [equation] at control
      cases control
    | answer value pick =>
      rw [equation] at controlValid control
      have same : rank=value := List.mem_singleton.mp control
      subst rank
      exact controlValid.mono expectation
    | scan later remaining tools good best =>
      rw [equation] at controlValid control
      have depth : later.length≤root := by have level:=controlValid.1;omega
      simp only [controlRanks,List.mem_cons,List.not_mem_nil,or_false] at control
      rcases control with rfl|rfl
      · exact controlValid.2.2.1.mono depth
      · exact controlValid.2.2.2.mono depth
  · obtain ⟨frame,member,rankMember⟩:=List.mem_flatMap.mp stack
    exact frame_ranks_bound frame (frames frame member).1 (frames frame member).2 rank rankMember

/-- All rank registers in EVERY actual state have an explicit finite code
0..N, plus the separate top code N+1. Tool IDs are already Fin q. -/
theorem actual_data_carrier (q : ℕ) (stages : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (clock : ℕ) :
    ∀ rank∈stateRanks (drive clock ⟨.call stages remaining,[]⟩),
      ∃ code : Fin (stages.length+2),decodeRank stages.length code.val=rank := by
  have valid:=(dfs_workspace q stages remaining clock).1
  intro rank member
  exact rank_finite_representation stages.length rank (state_ranks_bound _ valid rank member)

/-- Complete finite DFS algorithm subgoal, with exact original ties,
actual terminating next-step execution, a SINGLE F in its macro-step bound,
and an independent polynomial bound on every state of the SAME drive.
This theorem is not a Bool TM/WordISA or raw controller I/O theorem. -/
theorem generic_dfs_algorithm (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    ∃ steps final,
      drive steps ⟨.call stages remaining,[]⟩=final ∧ next final=none ∧
      final.control=.answer (PaperProofs.Structure.genericRank stages remaining)
        (match stages with
        | [] => none
        | eligible::later => PaperProofs.Structure.pickGenericMaxRankTool q eligible later remaining) ∧
      steps≤3*structuralFactor stages.length q ∧
      (∀ clock, WellFormed stages.length (drive clock ⟨.call stages remaining,[]⟩) ∧
        cells (drive clock ⟨.call stages remaining,[]⟩)≤workspace stages.length q) ∧
      (∀ clock rank, rank∈stateRanks (drive clock ⟨.call stages remaining,[]⟩) →
        ∃ code : Fin (stages.length+2),decodeRank stages.length code.val=rank) := by
  obtain ⟨steps,final,run,actual,halted,correct,cost⟩:=dfs_actual q stages remaining
  exact ⟨steps,final,actual,halted,correct,cost,dfs_workspace q stages remaining,
    actual_data_carrier q stages remaining⟩

end RootB23.GenericRank
