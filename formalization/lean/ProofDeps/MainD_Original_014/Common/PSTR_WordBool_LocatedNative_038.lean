module

public import Common.PSTR_WordBool_LocatedAlphabetRun_037
public import Common.PSTR_WordBool_StatementSpan_027

/-! Actual native instruction paths with physical head coordinates.
Statement time, endpoint, net displacement and static internal radius all
come from the SAME StatementSpan witness. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedNative

open Turing StatementClock StatementDisplacement

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]

abbrev Located (machine : Λ → TM1.Stmt Bool Λ σ) := NativeState machine × Int

def Step (machine : Λ → TM1.Stmt Bool Λ σ) (before after : Located machine) : Prop :=
  TM0.step (TM1to0.tr machine) before.1 = some after.1 ∧
    after.2 = before.2 + shift machine before.1

def annotate (machine : Λ → TM1.Stmt Bool Λ σ) (position : Int) :
    List (NativeState machine) → List (Located machine)
  | [] => []
  | first :: rest => (first, position) :: annotate machine (position + shift machine first) rest

theorem annotate_length (machine : Λ → TM1.Stmt Bool Λ σ)
    (trace : List (NativeState machine)) (position : Int) :
    (annotate machine position trace).length = trace.length := by
  induction trace generalizing position with
  | nil => rfl
  | cons first rest ih => simp only [annotate, List.length_cons, ih]

theorem annotate_positions (machine : Λ → TM1.Stmt Bool Λ σ)
    (first : NativeState machine) (rest : List (NativeState machine)) (position : Int) :
    (annotate machine position (first :: rest)).map Prod.snd =
      ((first :: rest).dropLast.map (shift machine)).scanl (· + ·) position := by
  induction rest generalizing first position with
  | nil => simp only [annotate, List.map_cons, List.map_nil, List.dropLast_singleton, List.scanl_nil]
  | cons next rest ih =>
    simpa only [annotate, List.map_cons, List.dropLast_cons_cons, List.scanl_cons] using
      congrArg (List.cons position) (ih next (position + shift machine first))

theorem annotate_chain (machine : Λ → TM1.Stmt Bool Λ σ)
    (first : NativeState machine) (rest : List (NativeState machine)) (position : Int)
    (chain : (first :: rest).IsChain
      (fun before after => TM0.step (TM1to0.tr machine) before = some after)) :
    (annotate machine position (first :: rest)).IsChain (Step machine) := by
  induction rest generalizing first position with
  | nil => exact List.isChain_singleton _
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    exact List.isChain_cons_cons.mpr ⟨⟨edge, rfl⟩, ih next _ tailChain⟩

theorem annotate_last (machine : Λ → TM1.Stmt Bool Λ σ)
    (first : NativeState machine) (rest : List (NativeState machine)) (final : NativeState machine)
    (position : Int) (last : (first :: rest).getLast? = some final) :
    (annotate machine position (first :: rest)).getLast? =
      some (final, position + traceMove machine (first :: rest)) := by
  induction rest generalizing first position with
  | nil =>
    have same : first = final := Option.some.inj last
    subst first
    simp only [annotate, List.getLast?_singleton, traceMove, List.dropLast_singleton,
      List.map_nil, List.sum_nil, Int.add_zero]
  | cons next rest ih =>
    have later := ih next (position + shift machine first) last
    simpa only [annotate, List.getLast?_cons_cons, move_cons machine first (next :: rest) (by simp),
      Int.add_assoc] using later

theorem statement_chunk (machine : Λ → TM1.Stmt Bool Λ σ)
    (statement : TM1.Stmt Bool Λ σ) (store : σ) (tape : Tape Bool) (position : Int) :
    ∃ posts : List (Located machine),
      1 ≤ posts.length ∧ posts.length ≤ weight statement ∧
      ((entry machine statement store tape, position) :: posts).IsChain (Step machine) ∧
      ((entry machine statement store tape, position) :: posts).getLast? =
        some (TM1to0.trCfg machine (TM1.stepAux statement store tape),
          position + netMove statement store tape) ∧
      ∀ point ∈ (entry machine statement store tape, position) :: posts,
        position - (weight statement : Int) ≤ point.2 ∧ point.2 ≤ position + (weight statement : Int) := by
  obtain ⟨posts, positive, length, chain, last, movement, coordinates⟩ :=
    StatementSpan.actual_statement_chunk machine statement store tape position
  let locatedPosts := annotate machine (position + shift machine (entry machine statement store tape)) posts
  have sameLength : locatedPosts.length = posts.length := annotate_length machine posts _
  have fullChain := annotate_chain machine (entry machine statement store tape) posts position chain
  have fullLast := annotate_last machine (entry machine statement store tape) posts
    (TM1to0.trCfg machine (TM1.stepAux statement store tape)) position
    ((StatementClock.prepend_last _ posts positive).trans last)
  rw [movement] at fullLast
  refine ⟨locatedPosts, by omega, by omega, fullChain, fullLast, ?_⟩
  intro point present
  have mapped : point.2 ∈ (annotate machine position (entry machine statement store tape :: posts)).map Prod.snd :=
    List.mem_map.mpr ⟨point, present, rfl⟩
  rw [annotate_positions] at mapped
  exact coordinates point.2 mapped

def compiledPoint (machine : Λ → TM1.Stmt Bool Λ σ) (point : LocatedAlphabet.Located Bool Λ σ) :
    Located machine := (TM1to0.trCfg machine point.1, point.2)

theorem step_path (machine : Λ → TM1.Stmt Bool Λ σ)
    (before after : LocatedAlphabet.Located Bool Λ σ)
    (edge : LocatedAlphabet.Step machine before after) (budget : Nat)
    (bounded : ∀ label, before.1.l = some label → weight (machine label) ≤ budget) :
    ∃ posts : List (Located machine),
      posts.length ≤ budget ∧
      (compiledPoint machine before :: posts).IsChain (Step machine) ∧
      (compiledPoint machine before :: posts).getLast? = some (compiledPoint machine after) ∧
      ∀ point ∈ compiledPoint machine before :: posts,
        before.2 - (budget : Int) ≤ point.2 ∧ point.2 ≤ before.2 + (budget : Int) := by
  rcases before with ⟨⟨label, store, tape⟩, position⟩
  cases label with
  | none => cases edge.1
  | some label =>
    have endpoint : TM1.stepAux (machine label) store tape = after.1 := Option.some.inj edge.1
    have endPosition : after.2 = position + netMove (machine label) store tape := edge.2
    obtain ⟨posts, _positive, length, chain, last, coordinates⟩ :=
      statement_chunk machine (machine label) store tape position
    have bound := bounded label rfl
    rw [endpoint] at last
    have lastAfter :
        ((entry machine (machine label) store tape, position) :: posts).getLast? =
          some (compiledPoint machine after) := by
      simpa only [compiledPoint, endPosition] using last
    refine ⟨posts, length.trans bound, chain, lastAfter, ?_⟩
    intro point present
    have within := coordinates point present
    constructor <;> omega

theorem compile_path (machine : Λ → TM1.Stmt Bool Λ σ)
    (before final : LocatedAlphabet.Located Bool Λ σ)
    (rest : List (LocatedAlphabet.Located Bool Λ σ))
    (chain : (before :: rest).IsChain (LocatedAlphabet.Step machine))
    (last : (before :: rest).getLast? = some final) (budget : Nat) (low high : Int)
    (weights : ∀ state ∈ before :: rest, ∀ label, state.1.l = some label → weight (machine label) ≤ budget)
    (sourceRange : ∀ state ∈ before :: rest, low ≤ state.2 ∧ state.2 ≤ high) :
    ∃ posts : List (Located machine),
      posts.length ≤ budget * rest.length ∧
      (compiledPoint machine before :: posts).IsChain (Step machine) ∧
      (compiledPoint machine before :: posts).getLast? = some (compiledPoint machine final) ∧
      ∀ point ∈ compiledPoint machine before :: posts,
        low - (budget : Int) ≤ point.2 ∧ point.2 ≤ high + (budget : Int) := by
  induction rest generalizing before with
  | nil =>
    have same : before = final := Option.some.inj last
    subst before
    refine ⟨[], by simp, List.isChain_singleton _, rfl, ?_⟩
    intro point present
    have same := List.mem_singleton.mp present
    subst point
    have within := sourceRange final List.mem_cons_self
    change low - (budget : Int) ≤ final.2 ∧ final.2 ≤ high + (budget : Int)
    constructor <;> omega
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have tailWeights : ∀ state ∈ next :: rest, ∀ label, state.1.l = some label →
        weight (machine label) ≤ budget := by
      intro state present label active
      exact weights state (List.mem_cons_of_mem _ present) label active
    have tailRange : ∀ state ∈ next :: rest, low ≤ state.2 ∧ state.2 ≤ high := by
      intro state present
      exact sourceRange state (List.mem_cons_of_mem _ present)
    obtain ⟨later, laterLength, laterChain, laterLast, laterRange⟩ := ih next tailChain last tailWeights tailRange
    obtain ⟨firstPosts, firstLength, firstChain, firstLast, firstRange⟩ :=
      step_path machine before next edge budget (weights before List.mem_cons_self)
    refine ⟨firstPosts ++ later, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_cons]
      exact (Nat.add_le_add firstLength laterLength).trans_eq
        ((Nat.add_comm budget (budget * rest.length)).trans (Nat.mul_succ budget rest.length).symm)
    · exact NativeTrace.join_chain _ _ _ firstLast firstChain laterChain
    · exact (NativeTrace.join_last _ _ _ firstLast).trans laterLast
    · intro point present
      have localToGlobal : ∀ point ∈ compiledPoint machine before :: firstPosts,
          low - (budget : Int) ≤ point.2 ∧ point.2 ≤ high + (budget : Int) := by
        intro point present
        have within := firstRange point present
        have sourceWithin := sourceRange before List.mem_cons_self
        constructor <;> omega
      rcases List.mem_cons.mp present with same | laterPoint
      · subst point
        exact localToGlobal _ List.mem_cons_self
      · rcases List.mem_append.mp laterPoint with first | later
        · exact localToGlobal point (List.mem_cons_of_mem _ first)
        · exact laterRange point (List.mem_cons_of_mem _ later)

end PaperProofs.Common.Native.PSTRWordBool.LocatedNative
