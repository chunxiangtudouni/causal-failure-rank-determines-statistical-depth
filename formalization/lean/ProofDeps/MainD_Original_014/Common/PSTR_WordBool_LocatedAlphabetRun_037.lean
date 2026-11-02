module

public import Common.PSTR_WordBool_LocatedAlphabet_036

/-! The whole alphabet compiler preserves a single actual located path.
Shared endpoints are identified once, and spatial slack depends on static
statement motion radius rather than the number of source transitions. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedAlphabetRun

open Turing StatementDisplacement AlphabetPrefix LocatedAlphabet

variable {Γ Λ σ : Type*} [Inhabited Γ]
variable {count : Nat} (encode : Γ → List.Vector Bool count)
    (decode : List.Vector Bool count → Γ)
    (pointed : encode default = List.Vector.replicate count false)
    (inverse : ∀ symbol, decode (encode symbol) = symbol)
    (machine : Λ → TM1.Stmt Γ Λ σ)

def compiledPoint (point : Located Γ Λ σ) : Located Bool (TM1to1.Λ' Γ Λ σ) σ :=
  (TM1to1.trCfg encode pointed point.1, (count : Int) * point.2)

include inverse

theorem step_path (before after : Located Γ Λ σ)
    (edge : Step machine before after) (radius : Nat)
    (bounded : ∀ label, before.1.l = some label → motionRadius (machine label) ≤ radius) :
    ∃ posts : List (Located Bool (TM1to1.Λ' Γ Λ σ) σ),
      (∀ label, before.1.l = some label → posts.length ≤ AlphabetClock.writes (machine label) + 1) ∧
      (compiledPoint encode pointed before :: posts).IsChain
        (Step (TM1to1.tr encode decode machine)) ∧
      (compiledPoint encode pointed before :: posts).getLast? =
        some (compiledPoint encode pointed after) ∧
      ∀ point ∈ compiledPoint encode pointed before :: posts,
        (count : Int) * before.2 - (count : Int) * (radius : Int) ≤ point.2 ∧
          point.2 ≤ (count : Int) * before.2 + (count : Int) * (radius : Int) := by
  rcases before with ⟨⟨label, store, tape⟩, position⟩
  cases label with
  | none => cases edge.1
  | some label =>
    obtain ⟨left, right, rfl⟩ := tape.exists_mk'
    have sourceEnd : TM1.stepAux (machine label) store (Tape.mk' left right) = after.1 :=
      Option.some.inj edge.1
    have sourcePosition : after.2 = position + netMove (machine label) store (Tape.mk' left right) := edge.2
    obtain ⟨posts, positive, length, first, chain, last, coordinates⟩ :=
      LocatedAlphabet.residual_trace encode decode pointed inverse machine (machine label)
        store left right ((count : Int) * position)
    rw [sourceEnd] at last
    have lastAfter : posts.getLast? = some (compiledPoint encode pointed after) := by
      simpa only [compiledPoint, sourcePosition, Int.mul_add] using last
    refine ⟨posts, ?_, ?_, ?_, ?_⟩
    · intro current active
      have same := Option.some.inj active
      subst current
      exact length
    · apply prepend_chain _ _ _ _ chain
      intro next present
      rw [first] at present
      have same := Option.some.inj (Option.mem_def.mp present)
      subst next
      constructor
      · change some (TM1.stepAux (TM1to1.trNormal decode (machine label)) store
          (TM1to1.trTape pointed (Tape.mk' left right))) = _
        rw [TM1to1.trTape_mk']
      · change (count : Int) * position + (count : Int) * leadingMove (machine label) store
          (Tape.mk' left right) = (count : Int) * position +
          netMove (TM1to1.trNormal decode (machine label)) store
            (TM1to1.trTape pointed (Tape.mk' left right))
        rw [normal_net encode decode pointed inverse]
    · exact (StatementClock.prepend_last _ posts positive).trans lastAfter
    · intro point present
      rcases List.mem_cons.mp present with same | later
      · subst point
        have positiveRadius : 0 ≤ (count : Int) * (radius : Int) := mul_nonneg (by omega) (by omega)
        change (count : Int) * position - (count : Int) * (radius : Int) ≤ (count : Int) * position ∧
          (count : Int) * position ≤ (count : Int) * position + (count : Int) * (radius : Int)
        constructor <;> omega
      · have within := coordinates point later
        have sourceBound := bounded label rfl
        have scaled : (count : Int) * (motionRadius (machine label) : Int) ≤
            (count : Int) * (radius : Int) := mul_le_mul_of_nonneg_left (by omega) (by omega)
        change (count : Int) * position - (count : Int) * (radius : Int) ≤ point.2 ∧
          point.2 ≤ (count : Int) * position + (count : Int) * (radius : Int)
        constructor <;> omega

theorem compile_path (before final : Located Γ Λ σ) (rest : List (Located Γ Λ σ))
    (chain : (before :: rest).IsChain (Step machine))
    (last : (before :: rest).getLast? = some final)
    (budget radius : Nat) (low high : Int)
    (counts : ∀ state ∈ before :: rest, ∀ label, state.1.l = some label →
      AlphabetClock.writes (machine label) + 1 ≤ budget ∧ motionRadius (machine label) ≤ radius)
    (sourceRange : ∀ state ∈ before :: rest, low ≤ state.2 ∧ state.2 ≤ high) :
    ∃ posts : List (Located Bool (TM1to1.Λ' Γ Λ σ) σ),
      posts.length ≤ budget * rest.length ∧
      (compiledPoint encode pointed before :: posts).IsChain
        (Step (TM1to1.tr encode decode machine)) ∧
      (compiledPoint encode pointed before :: posts).getLast? =
        some (compiledPoint encode pointed final) ∧
      ∀ point ∈ compiledPoint encode pointed before :: posts,
        (count : Int) * low - (count : Int) * (radius : Int) ≤ point.2 ∧
          point.2 ≤ (count : Int) * high + (count : Int) * (radius : Int) := by
  induction rest generalizing before with
  | nil =>
    have same : before = final := Option.some.inj last
    subst before
    refine ⟨[], by simp, List.isChain_singleton _, rfl, ?_⟩
    intro point present
    have same := List.mem_singleton.mp present
    subst point
    have within := sourceRange final List.mem_cons_self
    have lower : (count : Int) * low ≤ (count : Int) * final.2 :=
      mul_le_mul_of_nonneg_left within.1 (by omega)
    have upper : (count : Int) * final.2 ≤ (count : Int) * high :=
      mul_le_mul_of_nonneg_left within.2 (by omega)
    have positiveRadius : 0 ≤ (count : Int) * (radius : Int) := mul_nonneg (by omega) (by omega)
    change (count : Int) * low - (count : Int) * (radius : Int) ≤ (count : Int) * final.2 ∧
      (count : Int) * final.2 ≤ (count : Int) * high + (count : Int) * (radius : Int)
    constructor <;> omega
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have tailCounts : ∀ state ∈ next :: rest, ∀ label, state.1.l = some label →
        AlphabetClock.writes (machine label) + 1 ≤ budget ∧ motionRadius (machine label) ≤ radius := by
      intro state present label active
      exact counts state (List.mem_cons_of_mem _ present) label active
    have tailRange : ∀ state ∈ next :: rest, low ≤ state.2 ∧ state.2 ≤ high := by
      intro state present
      exact sourceRange state (List.mem_cons_of_mem _ present)
    obtain ⟨later, laterLength, laterChain, laterLast, laterRange⟩ := ih next tailChain last tailCounts tailRange
    have firstMotion : ∀ label, before.1.l = some label → motionRadius (machine label) ≤ radius := by
      intro label active
      exact (counts before List.mem_cons_self label active).2
    obtain ⟨firstPosts, firstLength, firstChain, firstLast, firstRange⟩ :=
      step_path encode decode pointed inverse machine before next edge radius firstMotion
    have firstBound : firstPosts.length ≤ budget := by
      cases active : before.1.l with
      | none =>
        rcases before with ⟨⟨current, memory, tape⟩, position⟩
        change current = none at active
        subst current
        cases edge.1
      | some label => exact (firstLength label active).trans (counts before List.mem_cons_self label active).1
    refine ⟨firstPosts ++ later, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_cons]
      exact (Nat.add_le_add firstBound laterLength).trans_eq
        ((Nat.add_comm budget (budget * rest.length)).trans (Nat.mul_succ budget rest.length).symm)
    · exact NativeTrace.join_chain _ _ _ firstLast firstChain laterChain
    · exact (NativeTrace.join_last _ _ _ firstLast).trans laterLast
    · intro point present
      have localToGlobal : ∀ point ∈ compiledPoint encode pointed before :: firstPosts,
          (count : Int) * low - (count : Int) * (radius : Int) ≤ point.2 ∧
            point.2 ≤ (count : Int) * high + (count : Int) * (radius : Int) := by
        intro point present
        have within := firstRange point present
        have beforeRange := sourceRange before List.mem_cons_self
        have lower : (count : Int) * low ≤ (count : Int) * before.2 :=
          mul_le_mul_of_nonneg_left beforeRange.1 (by omega)
        have upper : (count : Int) * before.2 ≤ (count : Int) * high :=
          mul_le_mul_of_nonneg_left beforeRange.2 (by omega)
        constructor <;> omega
      rcases List.mem_cons.mp present with same | laterPoint
      · subst point
        exact localToGlobal _ List.mem_cons_self
      · rcases List.mem_append.mp laterPoint with first | later
        · exact localToGlobal point (List.mem_cons_of_mem _ first)
        · exact laterRange point (List.mem_cons_of_mem _ later)

end PaperProofs.Common.Native.PSTRWordBool.LocatedAlphabetRun
