module

public import Common.PSTR_WordBool_AlphabetClock_005
public import Common.PSTR_WordBool_NativeTrace_006

/-! Whole actual source paths through the fixed alphabet compiler. This
retains each physical write continuation and its real transition. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AlphabetTrace

open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ]
variable {n : Nat} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
    (enc0 : enc default = List.Vector.replicate n false)
    (inverse : ∀ row, dec (enc row) = row)
    (machine : Λ → TM1.Stmt Γ Λ σ)

include inverse

theorem step_trace (label : Λ) (store : σ) (tape : Tape Γ) :
    ∃ posts : List (TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ),
      1 ≤ posts.length ∧ posts.length ≤ AlphabetClock.writes (machine label) + 1 ∧
      (TM1to1.trCfg enc enc0 ⟨some label, store, tape⟩ :: posts).IsChain
        (fun before after => TM1.step (TM1to1.tr enc dec machine) before = some after) ∧
      (TM1to1.trCfg enc enc0 ⟨some label, store, tape⟩ :: posts).getLast? =
        some (TM1to1.trCfg enc enc0 (TM1.stepAux (machine label) store tape)) := by
  obtain ⟨left, right, rfl⟩ := tape.exists_mk'
  obtain ⟨posts, positive, bound, head, chain, last⟩ :=
    AlphabetClock.residual_trace enc dec enc0 inverse machine (machine label) store left right
  have edge : TM1.step (TM1to1.tr enc dec machine)
      (TM1to1.trCfg enc enc0 ⟨some label, store, Tape.mk' left right⟩) = posts.head? := by
    simpa only [TM1.step, TM1to1.trCfg, Option.map_some, TM1to1.tr,
      TM1to1.trTape_mk'] using head.symm
  exact ⟨posts, positive, bound, AlphabetClock.cons_chain _ _ _ positive edge chain,
    (StatementClock.prepend_last _ _ positive).trans last⟩

theorem compile_path (budget : Nat) (start final : TM1.Cfg Γ Λ σ)
    (rest : List (TM1.Cfg Γ Λ σ))
    (chain : (start :: rest).IsChain (fun before after => TM1.step machine before = some after))
    (last : (start :: rest).getLast? = some final)
    (weights : ∀ state ∈ start :: rest, ∀ label, state.l = some label →
      AlphabetClock.writes (machine label) + 1 ≤ budget) :
    ∃ posts : List (TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ),
      posts.length ≤ budget * rest.length ∧
      (TM1to1.trCfg enc enc0 start :: posts).IsChain
        (fun before after => TM1.step (TM1to1.tr enc dec machine) before = some after) ∧
      (TM1to1.trCfg enc enc0 start :: posts).getLast? = some (TM1to1.trCfg enc enc0 final) := by
  induction rest generalizing start with
  | nil =>
    have same : start = final := Option.some.inj last
    subst start
    exact ⟨[], by simp, List.isChain_singleton _, rfl⟩
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have tailWeights : ∀ state ∈ next :: rest, ∀ label, state.l = some label →
        AlphabetClock.writes (machine label) + 1 ≤ budget := by
      intro state present label equal
      exact weights state (List.mem_cons_of_mem _ present) label equal
    obtain ⟨later, laterBound, laterChain, laterLast⟩ := ih next tailChain last tailWeights
    cases start with
    | mk label store tape =>
      cases label with
      | none => cases edge
      | some label =>
        have endpoint : TM1.stepAux (machine label) store tape = next := Option.some.inj edge
        obtain ⟨posts, positive, bound, chunkChain, chunkLast⟩ :=
          step_trace enc dec enc0 inverse machine label store tape
        have firstBound : posts.length ≤ budget :=
          bound.trans (weights ⟨some label, store, tape⟩ List.mem_cons_self label rfl)
        rw [endpoint] at chunkLast
        refine ⟨posts ++ later, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
        · exact NativeTrace.join_chain _ _ _ chunkLast chunkChain laterChain
        · exact (NativeTrace.join_last _ _ _ chunkLast).trans laterLast

end PaperProofs.Common.Native.PSTRWordBool.AlphabetTrace
