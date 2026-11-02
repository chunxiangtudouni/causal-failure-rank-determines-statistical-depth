module

public import Common.PSTR_WordBool_AlphabetPrefix_035
public import Common.PSTR_WordBool_NativeTrace_006
public import Mathlib.Algebra.Order.Ring.Int

/-! A single actual alphabet-compiled trace carries both its transition
count and exact physical coordinates. The coordinates are proof annotations,
never runtime labels, store fields, fuel or additional raw input. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedAlphabet

open Turing StatementDisplacement AlphabetPrefix

variable {Γ Λ σ : Type*} [Inhabited Γ]

abbrev Located (alphabet labels store : Type*) [Inhabited alphabet] :=
  TM1.Cfg alphabet labels store × Int

def net (machine : Λ → TM1.Stmt Γ Λ σ) (state : TM1.Cfg Γ Λ σ) : Int :=
  match state.l with
  | none => 0
  | some label => netMove (machine label) state.var state.Tape

def Step (machine : Λ → TM1.Stmt Γ Λ σ) (before after : Located Γ Λ σ) : Prop :=
  TM1.step machine before.1 = some after.1 ∧ after.2 = before.2 + net machine before.1

theorem prepend_chain {α : Type*} (relation : α → α → Prop) (first : α) (rest : List α)
    (edge : ∀ next ∈ rest.head?, relation first next) (chain : rest.IsChain relation) :
    (first :: rest).IsChain relation := List.isChain_cons.mpr ⟨edge, chain⟩

variable {count : Nat} (encode : Γ → List.Vector Bool count)
    (decode : List.Vector Bool count → Γ)
    (pointed : encode default = List.Vector.replicate count false)
    (inverse : ∀ symbol, decode (encode symbol) = symbol)
    (machine : Λ → TM1.Stmt Γ Λ σ)

include inverse

theorem residual_trace (statement : TM1.Stmt Γ Λ σ) (store : σ)
    (left right : ListBlank Γ) (position : Int) :
    ∃ trace : List (Located Bool (TM1to1.Λ' Γ Λ σ) σ),
      1 ≤ trace.length ∧ trace.length ≤ AlphabetClock.writes statement + 1 ∧
      trace.head? = some
        (TM1.stepAux (TM1to1.trNormal decode statement) store (TM1to1.trTape' pointed left right),
          position + (count : Int) * leadingMove statement store (Tape.mk' left right)) ∧
      trace.IsChain (Step (TM1to1.tr encode decode machine)) ∧
      trace.getLast? = some
        (TM1to1.trCfg encode pointed (TM1.stepAux statement store (Tape.mk' left right)),
          position + (count : Int) * netMove statement store (Tape.mk' left right)) ∧
      ∀ point ∈ trace,
        position - (count : Int) * (motionRadius statement : Int) ≤ point.2 ∧
          point.2 ≤ position + (count : Int) * (motionRadius statement : Int) := by
  induction statement generalizing store left right position with
  | halt =>
    refine ⟨[(TM1.stepAux (TM1to1.trNormal decode .halt) store
      (TM1to1.trTape' pointed left right), position)], le_rfl, le_rfl, ?_,
      List.isChain_singleton _, ?_, ?_⟩
    · simp only [List.head?_cons, leadingMove, Int.mul_zero, Int.add_zero]
    · simp only [List.getLast?_singleton, TM1to1.trNormal, TM1.stepAux, TM1to1.trCfg,
        TM1to1.trTape_mk', netMove, Int.mul_zero, Int.add_zero]; rfl
    · intro point present
      have same := List.mem_singleton.mp present
      subst point
      simp only [motionRadius, Int.natCast_zero, Int.mul_zero, Int.sub_zero, Int.add_zero,
        le_refl, and_self]
  | goto target =>
    refine ⟨[(TM1.stepAux (TM1to1.trNormal decode (.goto target)) store
      (TM1to1.trTape' pointed left right), position)], le_rfl, le_rfl, ?_,
      List.isChain_singleton _, ?_, ?_⟩
    · simp only [List.head?_cons, leadingMove, Int.mul_zero, Int.add_zero]
    · simp only [List.getLast?_singleton, TM1to1.trNormal,
        TM1to1.stepAux_read decode pointed inverse, TM1.stepAux, TM1to1.trCfg,
        TM1to1.trTape_mk', Tape.mk'_head, netMove, Int.mul_zero, Int.add_zero]; rfl
    · intro point present
      have same := List.mem_singleton.mp present
      subst point
      simp only [motionRadius, Int.natCast_zero, Int.mul_zero, Int.sub_zero, Int.add_zero,
        le_refl, and_self]
  | move direction tail ih =>
    cases direction with
    | left =>
      obtain ⟨trace, positive, length, first, chain, last, coordinates⟩ :=
        ih store left.tail (right.cons left.head) (position - count)
      refine ⟨trace, positive, length, ?_, chain, ?_, ?_⟩
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_move, TM1.stepAux,
          Tape.move_left_mk', TM1to1.trTape'_move_left pointed, leadingMove, delta,
          Int.mul_add, Int.mul_neg, Int.mul_one, sub_eq_add_neg, Int.add_assoc] using first
      · simpa only [TM1.stepAux, Tape.move_left_mk', netMove, delta, Int.mul_add,
          Int.mul_neg, Int.mul_one, sub_eq_add_neg, Int.add_assoc] using last
      · intro point present
        have within := coordinates point present
        simp only [motionRadius, Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]
        constructor <;> omega
    | right =>
      obtain ⟨trace, positive, length, first, chain, last, coordinates⟩ :=
        ih store (left.cons right.head) right.tail (position + count)
      refine ⟨trace, positive, length, ?_, chain, ?_, ?_⟩
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_move, TM1.stepAux,
          Tape.move_right_mk', TM1to1.trTape'_move_right pointed, leadingMove, delta,
          Int.mul_add, Int.mul_one, Int.add_assoc] using first
      · simpa only [TM1.stepAux, Tape.move_right_mk', netMove, delta, Int.mul_add,
          Int.mul_one, Int.add_assoc] using last
      · intro point present
        have within := coordinates point present
        simp only [motionRadius, Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]
        constructor <;> omega
  | load update tail ih =>
    simpa only [AlphabetClock.writes, TM1to1.trNormal,
      TM1to1.stepAux_read decode pointed inverse, TM1.stepAux, Tape.mk'_head,
      leadingMove, netMove, motionRadius] using
      ih (update right.head store) left right position
  | branch condition yes no ihYes ihNo =>
    cases choice : condition right.head store with
    | false =>
      obtain ⟨trace, positive, length, first, chain, last, coordinates⟩ :=
        ihNo store left right position
      refine ⟨trace, positive, ?_, ?_, chain, ?_, ?_⟩
      · change trace.length ≤ AlphabetClock.writes yes + AlphabetClock.writes no + 1
        omega
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_read decode pointed inverse,
          TM1.stepAux, leadingMove, Tape.mk'_head, choice, Bool.cond_false] using first
      · simpa only [TM1.stepAux, netMove, Tape.mk'_head, choice, Bool.cond_false] using last
      · intro point present
        have within := coordinates point present
        have extra : 0 ≤ (count : Int) * (motionRadius yes : Int) := mul_nonneg (by omega) (by omega)
        simp only [motionRadius, Int.natCast_add, Int.mul_add]
        constructor <;> omega
    | true =>
      obtain ⟨trace, positive, length, first, chain, last, coordinates⟩ :=
        ihYes store left right position
      refine ⟨trace, positive, ?_, ?_, chain, ?_, ?_⟩
      · change trace.length ≤ AlphabetClock.writes yes + AlphabetClock.writes no + 1
        omega
      · simpa only [TM1to1.trNormal, TM1to1.stepAux_read decode pointed inverse,
          TM1.stepAux, leadingMove, Tape.mk'_head, choice, Bool.cond_true] using first
      · simpa only [TM1.stepAux, netMove, Tape.mk'_head, choice, Bool.cond_true] using last
      · intro point present
        have within := coordinates point present
        have extra : 0 ≤ (count : Int) * (motionRadius no : Int) := mul_nonneg (by omega) (by omega)
        simp only [motionRadius, Int.natCast_add, Int.mul_add]
        constructor <;> omega
  | write update tail ih =>
    obtain ⟨old, right, rfl⟩ := right.exists_cons
    obtain ⟨trace, positive, length, first, chain, last, coordinates⟩ :=
      ih store left (right.cons (update old store)) position
    let start : Located Bool (TM1to1.Λ' Γ Λ σ) σ :=
      (TM1.stepAux (TM1to1.trNormal decode (.write update tail)) store
        (TM1to1.trTape' pointed left (right.cons old)), position)
    have startCfg : start.1 =
        ⟨some (.write (update old store) tail), store, TM1to1.trTape' pointed left (right.cons old)⟩ := by
      simp only [start, TM1to1.trNormal, TM1to1.stepAux_read decode pointed inverse,
        TM1.stepAux, ListBlank.head_cons]
    have nextEdge : ∀ next ∈ trace.head?, Step (TM1to1.tr encode decode machine) start next := by
      intro next present
      rw [first] at present
      have same := Option.some.inj (Option.mem_def.mp present)
      subst next
      constructor
      · rw [startCfg]
        simp only [TM1.step, TM1to1.tr, TM1to1.stepAux_write, TM1to1.stepAux_move,
          TM1to1.trTape'_move_left pointed, ListBlank.tail_cons, ListBlank.head_cons]
      · change position + (count : Int) * leadingMove tail store
          (Tape.mk' left (right.cons (update old store))) = position + net _ start.1
        rw [startCfg]
        dsimp only [net]
        rw [write_continuation_net encode decode pointed inverse]
    refine ⟨start :: trace, by simp, ?_, ?_, prepend_chain _ _ _ nextEdge chain, ?_, ?_⟩
    · change trace.length + 1 ≤ (AlphabetClock.writes tail + 1) + 1
      omega
    · simp only [List.head?_cons, start, leadingMove, Int.mul_zero, Int.add_zero]
    · rw [StatementClock.prepend_last _ _ positive]
      simpa only [TM1.stepAux, Tape.mk'_head, Tape.write_mk', ListBlank.head_cons,
        ListBlank.tail_cons, netMove] using last
    · intro point present
      rcases List.mem_cons.mp present with same | later
      · subst point
        have positiveRadius : 0 ≤ (count : Int) * (motionRadius tail : Int) :=
          mul_nonneg (by omega) (by omega)
        change position - (count : Int) * (motionRadius tail : Int) ≤ position ∧
          position ≤ position + (count : Int) * (motionRadius tail : Int)
        constructor <;> omega
      · exact coordinates point later

end PaperProofs.Common.Native.PSTRWordBool.LocatedAlphabet
