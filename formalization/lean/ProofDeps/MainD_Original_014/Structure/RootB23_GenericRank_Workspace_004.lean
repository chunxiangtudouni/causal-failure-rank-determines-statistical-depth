module
public import Structure.RootB23_GenericRank_Machine_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.GenericRank

def RankBound (limit : ℕ) (rank : ℕ∞) : Prop := rank=⊤ ∨ rank≤(limit : ℕ∞)

theorem RankBound.mono {small large : ℕ} {rank : ℕ∞}
    (bounded : RankBound small rank) (bound : small≤large) : RankBound large rank := by
  rcases bounded with infinite|finite
  · exact Or.inl infinite
  · exact Or.inr (finite.trans (by exact_mod_cast bound))

theorem rankBound_zero (limit : ℕ) : RankBound limit 0 := Or.inr (by exact zero_le)

theorem rankBound_max {limit : ℕ} {first later : ℕ∞}
    (one : RankBound limit first) (two : RankBound limit later) : RankBound limit (max first later) := by
  rcases one with rfl|one
  · exact Or.inl (max_eq_left le_top)
  rcases two with rfl|two
  · exact Or.inl (max_eq_right le_top)
  · exact Or.inr (max_le one two)

theorem rankBound_update {q limit : ℕ} (best : Best q) (tool : Fin q) (rank : ℕ∞)
    (one : RankBound limit (bestRank best)) (two : RankBound limit rank) :
    RankBound limit (bestRank (update best tool rank)) := by
  rw [bestRank_update]
  exact rankBound_max one two

theorem rankBound_min_succ {limit : ℕ} {good bad : ℕ∞}
    (one : RankBound limit good) (two : RankBound limit bad) :
    RankBound (limit+1) (min good (1+bad)) := by
  rcases one with rfl|one
  · rcases two with rfl|two
    · exact Or.inl (by simp)
    · apply Or.inr
      calc
        min ⊤ (1+bad)≤1+bad := min_le_right _ _
        _≤1+(limit : ℕ∞) := add_le_add (le_refl (1 : ℕ∞)) two
        _=((limit+1 : ℕ) : ℕ∞) := by
          rw [ENat.natCast_add,ENat.natCast_one,add_comm]
  · apply Or.inr
    exact (min_le_left _ _).trans (one.trans (by exact_mod_cast Nat.le_succ limit))

def frameDepth {q : ℕ} : Frame q → ℕ
  | .good later _ _ => later.length
  | .bad later _ _ _ _ _ => later.length

def pending {q : ℕ} : Frame q → List (Fin q)
  | .good _ _ tools => tools
  | .bad _ _ tools _ _ _ => tools

def FrameValid {q : ℕ} : Frame q → Prop
  | .good _ _ tools => tools.length≤q
  | .bad later _ tools good best _ =>
      tools.length≤q ∧ RankBound later.length good ∧ RankBound later.length (bestRank best)

def expected {q : ℕ} (root : ℕ) : List (Frame q) → ℕ
  | [] => root
  | frame::_ => frameDepth frame

def StackValid {q : ℕ} (root : ℕ) : List (Frame q) → Prop
  | [] => True
  | frame::rest => StackValid root rest ∧ FrameValid frame ∧ frameDepth frame+1≤expected root rest

def ControlValid {q : ℕ} (limit : ℕ) : Control q → Prop
  | .call stages _ => stages.length≤limit
  | .answer rank _ => RankBound limit rank
  | .scan later _ tools good best =>
      later.length+1≤limit ∧ tools.length≤q ∧
      RankBound later.length good ∧ RankBound later.length (bestRank best)

def WellFormed {q : ℕ} (root : ℕ) (state : State q) : Prop :=
  StackValid root state.stack ∧ ControlValid (expected root state.stack) state.control

theorem stack_depth_bound {q root : ℕ} (stack : List (Frame q)) (valid : StackValid root stack) :
    expected root stack+stack.length≤root := by
  induction stack with
  | nil => exact le_refl _
  | cons frame rest ih =>
    rcases valid with ⟨restValid,frameValid,level⟩
    have bound:=ih restValid
    change frameDepth frame+(rest.length+1)≤root
    omega

theorem expected_le {q root : ℕ} (stack : List (Frame q)) (valid : StackValid root stack) :
    expected root stack≤root := by have bound:=stack_depth_bound stack valid;omega

def tick {q : ℕ} (state : State q) : State q := (next state).getD state

/-- The finite rank carrier is maintained by syntactic depth, not by an
assumption that an externally supplied answer is correct. -/
theorem tick_wellFormed {q root : ℕ} (state : State q) (valid : WellFormed root state) :
    WellFormed root (tick state) := by
  rcases state with ⟨control,stack⟩
  rcases valid with ⟨stackValid,controlValid⟩
  cases control with
  | call stages remaining =>
    cases stages with
    | nil =>
      change StackValid root stack ∧ RankBound (expected root stack) ⊤
      exact ⟨stackValid,Or.inl rfl⟩
    | cons eligible later =>
      change StackValid root (.good later remaining
        (PaperProofs.Structure.genericRankCandidates q eligible remaining)::stack) ∧ later.length≤later.length
      exact ⟨⟨stackValid,candidates_length q eligible remaining,controlValid⟩,le_refl _⟩
  | answer rank pick =>
    cases stack with
    | nil => exact ⟨stackValid,controlValid⟩
    | cons frame rest =>
      rcases stackValid with ⟨restValid,frameValid,level⟩
      cases frame with
      | good later remaining tools =>
        change StackValid root rest ∧ later.length+1≤expected root rest ∧ tools.length≤q ∧
          RankBound later.length rank ∧ RankBound later.length (bestRank (none : Best q))
        exact ⟨restValid,level,frameValid,controlValid,rankBound_zero _⟩
      | bad later remaining tools good best tool =>
        rcases frameValid with ⟨toolsBound,goodBound,bestBound⟩
        change StackValid root rest ∧ later.length+1≤expected root rest ∧ tools.length≤q ∧
          RankBound later.length good ∧ RankBound later.length (bestRank (update best tool rank))
        exact ⟨restValid,level,toolsBound,goodBound,rankBound_update best tool rank bestBound controlValid⟩
  | scan later remaining tools good best =>
    rcases controlValid with ⟨level,toolsBound,goodBound,bestBound⟩
    cases tools with
    | nil =>
      change StackValid root stack ∧ RankBound (expected root stack) (min good (1+bestRank best))
      exact ⟨stackValid,(rankBound_min_succ goodBound bestBound).mono level⟩
    | cons tool tools =>
      change StackValid root (.bad later remaining tools good best tool::stack) ∧ later.length≤later.length
      refine ⟨⟨stackValid,?_,level⟩,le_refl _⟩
      exact ⟨Nat.le_of_succ_le toolsBound,goodBound,bestBound⟩

theorem drive_wellFormed {q root : ℕ} (count : ℕ) (state : State q) (valid : WellFormed root state) :
    WellFormed root (drive count state) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (tick state) (tick_wellFormed state valid)

theorem frame_bounds {q root : ℕ} (stack : List (Frame q)) (valid : StackValid root stack) :
    ∀ frame∈stack, FrameValid frame ∧ frameDepth frame≤root := by
  induction stack with
  | nil => intro frame member;cases member
  | cons first rest ih =>
    rcases valid with ⟨restValid,frameValid,level⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl|member
    · have bound:=expected_le rest restValid
      exact ⟨frameValid,by omega⟩
    · exact ih restValid frame member

/-- Explicit finite payload accounting: suffix incidence uses one q-bit
row and header per stage, remaining uses q bits, tools use one ID each;
fixed scalar/rank/frame headers are included in12 slots. No write history. -/
def frameCells {q : ℕ} (frame : Frame q) : ℕ :=
  12+frameDepth frame*(q+1)+q+(pending frame).length

def controlCells {q : ℕ} : Control q → ℕ
  | .call stages _ => 6+stages.length*(q+1)+q
  | .answer _ _ => 5
  | .scan later _ tools _ _ => 12+later.length*(q+1)+q+tools.length

def cells {q : ℕ} (state : State q) : ℕ := controlCells state.control+(state.stack.map frameCells).sum
def workspace (N q : ℕ) : ℕ := (N+1)*(12+N*(q+1)+2*q)

theorem frame_cells_bound {q root : ℕ} (frame : Frame q)
    (valid : FrameValid frame) (depth : frameDepth frame≤root) :
    frameCells frame≤12+root*(q+1)+2*q := by
  have product:=Nat.mul_le_mul_right (q+1) depth
  have tools : (pending frame).length≤q := by
    cases frame with
    | good => exact valid
    | bad => exact valid.1
  unfold frameCells
  omega

theorem sum_frame_cells {q : ℕ} (stack : List (Frame q)) (limit : ℕ)
    (bound : ∀ frame∈stack,frameCells frame≤limit) :
    (stack.map frameCells).sum≤stack.length*limit := by
  induction stack with
  | nil => simp
  | cons first rest ih =>
    have firstBound:=bound first (List.mem_cons_self)
    have restBound:=ih (fun frame member => bound frame (List.mem_cons_of_mem first member))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem wellFormed_cells {q root : ℕ} (state : State q) (valid : WellFormed root state) :
    cells state≤workspace root q := by
  rcases valid with ⟨stackValid,controlValid⟩
  have depth:=stack_depth_bound state.stack stackValid
  have expectation:=expected_le state.stack stackValid
  have every:=frame_bounds state.stack stackValid
  have stored:=sum_frame_cells state.stack (12+root*(q+1)+2*q)
    (fun frame member => frame_cells_bound frame (every frame member).1 (every frame member).2)
  have stackCount : state.stack.length≤root := by omega
  have storedBound:=Nat.mul_le_mul_right (12+root*(q+1)+2*q) stackCount
  have controlBound : controlCells state.control≤12+root*(q+1)+2*q := by
    cases h : state.control with
    | call stages remaining =>
      rw [h] at controlValid
      have stagesBound : stages.length≤root := controlValid.trans expectation
      have product:=Nat.mul_le_mul_right (q+1) stagesBound
      simp only [controlCells]
      omega
    | answer rank pick => simp only [controlCells];omega
    | scan later remaining tools good best =>
      rw [h] at controlValid
      rcases controlValid with ⟨level,toolsBound,goodBound,bestBound⟩
      have stagesBound : later.length≤root := by omega
      have product:=Nat.mul_le_mul_right (q+1) stagesBound
      simp only [controlCells]
      omega
  unfold cells workspace
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- EVERY actual deterministic prefix, including any clock after halt,
has this same polynomial workspace bound independent of F. -/
theorem dfs_workspace (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) (clock : ℕ) :
    WellFormed stages.length (drive clock ⟨.call stages remaining,[]⟩) ∧
    cells (drive clock ⟨.call stages remaining,[]⟩)≤workspace stages.length q := by
  have initial : WellFormed stages.length (⟨.call stages remaining,[]⟩ : State q) := ⟨trivial,le_refl _⟩
  have actual:=drive_wellFormed clock _ initial
  exact ⟨actual,wellFormed_cells _ actual⟩

end RootB23.GenericRank
