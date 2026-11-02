module

public import Common.PSTR_WordBool_StatementClock_002

/-! Actual concatenation of native statement traces, retaining ONE endpoint
for adjoining chunks. No transition, duplicate boundary or HALT is free. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NativeTrace

open Turing

theorem join_chain {α : Type*} {relation : α → α → Prop}
    (frontPart : List α) (middle : α) (suffix : List α)
    (last : frontPart.getLast? = some middle) (firstChain : frontPart.IsChain relation)
    (secondChain : (middle :: suffix).IsChain relation) :
    (frontPart ++ suffix).IsChain relation := by
  cases frontPart with
  | nil => simp at last
  | cons first rest =>
    induction rest generalizing first with
    | nil =>
      have same : first = middle := Option.some.inj last
      subst first
      exact secondChain
    | cons next rest ih =>
      obtain ⟨edge, tail⟩ := List.isChain_cons_cons.mp firstChain
      exact List.isChain_cons_cons.mpr ⟨edge, ih next last tail⟩

theorem join_last {α : Type*} (frontPart : List α) (middle : α) (suffix : List α)
    (last : frontPart.getLast? = some middle) :
    (frontPart ++ suffix).getLast? = (middle :: suffix).getLast? := by
  cases suffix with
  | nil => simpa using last
  | cons head tail =>
    calc
      (frontPart ++ head :: tail).getLast? = (head :: tail).getLast? :=
        List.getLast?_append_cons frontPart head tail
      _ = (middle :: head :: tail).getLast? := List.getLast?_cons_cons.symm

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]

theorem compile_path (machine : Λ → TM1.Stmt Bool Λ σ) (budget : Nat)
    (start final : TM1.Cfg Bool Λ σ) (rest : List (TM1.Cfg Bool Λ σ))
    (chain : (start :: rest).IsChain (fun before after => TM1.step machine before = some after))
    (last : (start :: rest).getLast? = some final)
    (weights : ∀ state ∈ start :: rest, ∀ label, state.l = some label →
      StatementClock.weight (machine label) ≤ budget) :
    ∃ posts : List (TM0.Cfg Bool (TM1to0.Λ' machine)),
      posts.length ≤ budget * rest.length ∧
      (TM1to0.trCfg machine start :: posts).IsChain
        (fun before after => TM0.step (TM1to0.tr machine) before = some after) ∧
      (TM1to0.trCfg machine start :: posts).getLast? = some (TM1to0.trCfg machine final) := by
  induction rest generalizing start with
  | nil =>
    have same : start = final := Option.some.inj last
    subst start
    exact ⟨[], by simp, List.isChain_singleton _, rfl⟩
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have tailWeights : ∀ state ∈ next :: rest, ∀ label, state.l = some label →
        StatementClock.weight (machine label) ≤ budget := by
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
          StatementClock.statement_chunk machine (machine label) store tape
        have firstBound : posts.length ≤ budget :=
          bound.trans (weights ⟨some label, store, tape⟩ (List.mem_cons_self) label rfl)
        rw [endpoint] at chunkLast
        have fullLast :
            (TM1to0.trCfg machine ⟨some label, store, tape⟩ :: posts).getLast? =
              some (TM1to0.trCfg machine next) :=
          (StatementClock.prepend_last _ posts positive).trans chunkLast
        refine ⟨posts ++ later, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
        · exact join_chain _ _ _ fullLast chunkChain laterChain
        · exact (join_last _ _ _ fullLast).trans laterLast

end PaperProofs.Common.Native.PSTRWordBool.NativeTrace
