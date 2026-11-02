module

public import Common.PSTR_WordBool_StatementDisplacement_026

/-! Real internal native head positions stay within a STATIC source-statement
radius. Local chunk length is bounded by fixed syntax, never by total elapsed
source time. Combined with exact net displacement this can be composed across
bounded physical scanner endpoints without introducing a second time factor. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.StatementSpan

open Turing StatementClock StatementDisplacement

theorem scan_range (steps : List Int) (position : Int)
    (bounded : ∀ step ∈ steps, -1 ≤ step ∧ step ≤ 1) :
    ∀ point ∈ steps.scanl (· + ·) position,
      position - (steps.length : Int) ≤ point ∧ point ≤ position + (steps.length : Int) := by
  induction steps generalizing position with
  | nil =>
    intro point present
    simp only [List.scanl_nil, List.mem_singleton] at present
    subst point
    constructor <;> omega
  | cons first rest ih =>
    have firstBound := bounded first List.mem_cons_self
    have tailBound : ∀ step ∈ rest, -1 ≤ step ∧ step ≤ 1 := by
      intro step present
      exact bounded step (List.mem_cons_of_mem _ present)
    intro point present
    rw [List.scanl_cons] at present
    rcases List.mem_cons.mp present with same | later
    · subst point
      constructor <;> omega
    · have within := ih (position + first) tailBound point later
      simp only [List.length_cons]
      constructor <;> omega

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]

theorem shift_bounds (machine : Λ → TM1.Stmt Bool Λ σ) (state : NativeState machine) :
    -1 ≤ shift machine state ∧ shift machine state ≤ 1 := by
  cases instruction : (TM1to0.tr machine) state.q state.Tape.head with
  | none => simp only [shift, instruction]; omega
  | some next =>
    obtain ⟨label, statement⟩ := next
    cases statement with
    | move direction =>
      cases direction <;> simp only [shift, instruction] <;> omega
    | write bit => simp only [shift, instruction]; omega

theorem chunk_range (machine : Λ → TM1.Stmt Bool Λ σ) (first : NativeState machine)
    (posts : List (NativeState machine)) (position : Int) (budget : Nat)
    (length : posts.length ≤ budget) :
    ∀ point ∈ ((first :: posts).dropLast.map (shift machine)).scanl (· + ·) position,
      position - (budget : Int) ≤ point ∧ point ≤ position + (budget : Int) := by
  have bounded : ∀ step ∈ (first :: posts).dropLast.map (shift machine), -1 ≤ step ∧ step ≤ 1 := by
    intro step present
    obtain ⟨state, _, equal⟩ := List.mem_map.mp present
    subst step
    exact shift_bounds machine state
  intro point present
  have within := scan_range _ position bounded point present
  simp only [List.length_map, List.length_dropLast_cons] at within
  constructor <;> omega

theorem actual_statement_chunk (machine : Λ → TM1.Stmt Bool Λ σ)
    (statement : TM1.Stmt Bool Λ σ) (store : σ) (tape : Tape Bool) (position : Int) :
    ∃ posts : List (NativeState machine),
      1 ≤ posts.length ∧ posts.length ≤ weight statement ∧
      (entry machine statement store tape :: posts).IsChain
        (fun before after => TM0.step (TM1to0.tr machine) before = some after) ∧
      posts.getLast? = some (TM1to0.trCfg machine (TM1.stepAux statement store tape)) ∧
      traceMove machine (entry machine statement store tape :: posts) = netMove statement store tape ∧
      ∀ point ∈ ((entry machine statement store tape :: posts).dropLast.map (shift machine)).scanl (· + ·) position,
        position - (weight statement : Int) ≤ point ∧ point ≤ position + (weight statement : Int) := by
  obtain ⟨posts, positive, length, chain, last, movement⟩ :=
    StatementDisplacement.statement_chunk machine statement store tape
  exact ⟨posts, positive, length, chain, last, movement,
    chunk_range machine _ posts position (weight statement) length⟩

end PaperProofs.Common.Native.PSTRWordBool.StatementSpan
