module

public import Common.PSTR_WordBool_StatementClock_002

/-! A quantitative refinement of Mathlib's alphabet compiler. Every source
write gives at most one extra TM1 macro transition. The Bool scans inside a
macro still require 002's ACTUAL native statement clock when consumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AlphabetClock

open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ]

def writes : TM1.Stmt Γ Λ σ → Nat
  | .move _ tail => writes tail
  | .write _ tail => writes tail + 1
  | .load _ tail => writes tail
  | .branch _ left right => writes left + writes right
  | .goto _ => 0
  | .halt => 0

theorem cons_chain {α : Type*} (step : α → Option α) (start : α) (trace : List α)
    (nonempty : 1 ≤ trace.length)
    (edge : step start = trace.head?)
    (chain : trace.IsChain (fun before after => step before = some after)) :
    (start :: trace).IsChain (fun before after => step before = some after) := by
  cases trace with
  | nil => simp at nonempty
  | cons first rest => exact List.isChain_cons_cons.mpr ⟨edge, chain⟩

variable {n : Nat} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
    (enc0 : enc default = List.Vector.replicate n false)
    (inverse : ∀ row, dec (enc row) = row)
    (machine : Λ → TM1.Stmt Γ Λ σ)

include inverse

theorem residual_trace (statement : TM1.Stmt Γ Λ σ) (store : σ)
    (left right : ListBlank Γ) :
    ∃ trace : List (TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ),
      1 ≤ trace.length ∧ trace.length ≤ writes statement + 1 ∧
      trace.head? = some (TM1.stepAux (TM1to1.trNormal dec statement) store
        (TM1to1.trTape' enc0 left right)) ∧
      trace.IsChain (fun before after => TM1.step (TM1to1.tr enc dec machine) before = some after) ∧
      trace.getLast? = some (TM1to1.trCfg enc enc0
        (TM1.stepAux statement store (Tape.mk' left right))) := by
  induction statement generalizing store left right with
  | halt =>
    refine ⟨[TM1.stepAux (TM1to1.trNormal dec .halt) store
      (TM1to1.trTape' enc0 left right)], le_rfl, le_rfl, rfl, List.isChain_singleton _, ?_⟩
    simp only [TM1to1.trNormal, TM1.stepAux, TM1to1.trCfg, TM1to1.trTape_mk']; rfl
  | goto target =>
    refine ⟨[TM1.stepAux (TM1to1.trNormal dec (.goto target)) store
      (TM1to1.trTape' enc0 left right)], le_rfl, le_rfl, rfl, List.isChain_singleton _, ?_⟩
    simp only [TM1to1.trNormal, TM1to1.stepAux_read dec enc0 inverse,
      TM1.stepAux, TM1to1.trCfg, TM1to1.trTape_mk', Tape.mk'_head]; rfl
  | move direction tail ih =>
    cases direction with
    | left =>
      simpa only [writes, TM1to1.trNormal, TM1to1.stepAux_move, TM1.stepAux,
        Tape.move_left_mk', TM1to1.trTape'_move_left enc0] using
        ih store left.tail (right.cons left.head)
    | right =>
      simpa only [writes, TM1to1.trNormal, TM1to1.stepAux_move, TM1.stepAux,
        Tape.move_right_mk', TM1to1.trTape'_move_right enc0] using
        ih store (left.cons right.head) right.tail
  | load update tail ih =>
    simpa only [writes, TM1to1.trNormal, TM1to1.stepAux_read dec enc0 inverse,
      TM1.stepAux, Tape.mk'_head] using ih (update right.head store) left right
  | branch condition first second firstIH secondIH =>
    cases decision : condition right.head store with
    | false =>
      obtain ⟨trace, positive, bound, head, chain, last⟩ := secondIH store left right
      refine ⟨trace, positive, by change trace.length ≤ writes first + writes second + 1; omega,
        ?_, chain, ?_⟩
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_read dec enc0 inverse,
          TM1.stepAux, decision, Bool.cond_false] using head
      · simpa only [TM1.stepAux, Tape.mk'_head, decision, Bool.cond_false] using last
    | true =>
      obtain ⟨trace, positive, bound, head, chain, last⟩ := firstIH store left right
      refine ⟨trace, positive, by change trace.length ≤ writes first + writes second + 1; omega,
        ?_, chain, ?_⟩
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_read dec enc0 inverse,
          TM1.stepAux, decision, Bool.cond_true] using head
      · simpa only [TM1.stepAux, Tape.mk'_head, decision, Bool.cond_true] using last
  | write update tail ih =>
    obtain ⟨old, right, rfl⟩ := right.exists_cons
    obtain ⟨trace, positive, bound, head, chain, last⟩ :=
      ih store left (right.cons (update old store))
    let start : TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ :=
      TM1.stepAux (TM1to1.trNormal dec (.write update tail)) store
        (TM1to1.trTape' enc0 left (right.cons old))
    have edge : TM1.step (TM1to1.tr enc dec machine) start = trace.head? := by
      rw [head]
      simp only [start, TM1to1.trNormal, TM1to1.stepAux_read dec enc0 inverse,
        TM1.stepAux, ListBlank.head_cons, TM1.step, TM1to1.tr,
        TM1to1.stepAux_write, TM1to1.stepAux_move, TM1to1.trTape'_move_left enc0,
        ListBlank.tail_cons]
    refine ⟨start :: trace, by simp, ?_, rfl,
      cons_chain _ _ _ positive edge chain, ?_⟩
    · change trace.length + 1 ≤ (writes tail + 1) + 1
      omega
    · rw [StatementClock.prepend_last _ _ positive]
      simpa only [TM1.stepAux, Tape.mk'_head, Tape.write_mk', ListBlank.head_cons,
        ListBlank.tail_cons] using last

end PaperProofs.Common.Native.PSTRWordBool.AlphabetClock
