module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Chain

/-! Quantitative real TM0 traces for Mathlib's TM1 statement compiler.
The count is the number of actual native transitions, including the dummy
writes for goto and halt. Finite control closure and original Bool codecs
remain separate obligations when this generic compiler lemma is consumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.StatementClock

open Turing

variable {Λ σ : Type*}

def weight : TM1.Stmt Bool Λ σ → Nat
  | .move _ tail => weight tail + 1
  | .write _ tail => weight tail + 1
  | .load _ tail => weight tail + 1
  | .branch _ left right => weight left + weight right + 1
  | .goto _ => 1
  | .halt => 1

abbrev NativeState (machine : Λ → TM1.Stmt Bool Λ σ) := TM0.Cfg Bool (TM1to0.Λ' machine)

def entry (machine : Λ → TM1.Stmt Bool Λ σ) (statement : TM1.Stmt Bool Λ σ)
    (store : σ) (tape : Tape Bool) : NativeState machine := ⟨(some statement, store), tape⟩

theorem replace_first {α : Type*} (step : α → Option α) (original replacement : α)
    (posts : List α) (positive : 1 ≤ posts.length) (same : step replacement = step original)
    (chain : (original :: posts).IsChain (fun before after => step before = some after)) :
    (replacement :: posts).IsChain (fun before after => step before = some after) := by
  cases posts with
  | nil => simp at positive
  | cons first rest =>
    obtain ⟨edge, tail⟩ := List.isChain_cons_cons.mp chain
    exact List.isChain_cons_cons.mpr ⟨same.trans edge, tail⟩

theorem prepend_last {α : Type*} (first : α) (posts : List α) (positive : 1 ≤ posts.length) :
    (first :: posts).getLast? = posts.getLast? := by
  cases posts with
  | nil => simp at positive
  | cons head tail => rfl

variable [Inhabited Λ] [Inhabited σ]

theorem statement_chunk (machine : Λ → TM1.Stmt Bool Λ σ)
    (statement : TM1.Stmt Bool Λ σ) (store : σ) (tape : Tape Bool) :
    ∃ posts : List (NativeState machine),
      1 ≤ posts.length ∧ posts.length ≤ weight statement ∧
      (entry machine statement store tape :: posts).IsChain
        (fun before after => TM0.step (TM1to0.tr machine) before = some after) ∧
      posts.getLast? = some (TM1to0.trCfg machine (TM1.stepAux statement store tape)) := by
  induction statement generalizing store tape with
  | halt =>
    let final := TM1to0.trCfg machine (TM1.stepAux .halt store tape)
    have first : TM0.step (TM1to0.tr machine) (entry machine .halt store tape) = some final := by
      change (some ⟨(none, store), tape.write tape.head⟩ : Option (NativeState machine)) = some final
      rw [Tape.write_self]
      rfl
    refine ⟨[final], le_rfl, le_rfl, ?_, rfl⟩
    exact List.isChain_cons_cons.mpr ⟨first, List.isChain_singleton _⟩
  | goto target =>
    let final := TM1to0.trCfg machine (TM1.stepAux (.goto target) store tape)
    have first : TM0.step (TM1to0.tr machine) (entry machine (.goto target) store tape) = some final := by
      change (some ⟨(some (machine (target tape.head store)), store), tape.write tape.head⟩ :
        Option (NativeState machine)) = some final
      rw [Tape.write_self]
      rfl
    refine ⟨[final], le_rfl, le_rfl, ?_, rfl⟩
    exact List.isChain_cons_cons.mpr ⟨first, List.isChain_singleton _⟩
  | move direction tail ih =>
    obtain ⟨posts, positive, bound, chain, last⟩ := ih store (tape.move direction)
    refine ⟨entry machine tail store (tape.move direction) :: posts, by simp, ?_, ?_, ?_⟩
    · exact Nat.succ_le_succ bound
    · exact List.isChain_cons_cons.mpr ⟨rfl, chain⟩
    · exact (prepend_last _ posts positive).trans last
  | write update tail ih =>
    obtain ⟨posts, positive, bound, chain, last⟩ := ih store (tape.write (update tape.head store))
    refine ⟨entry machine tail store (tape.write (update tape.head store)) :: posts, by simp, ?_, ?_, ?_⟩
    · exact Nat.succ_le_succ bound
    · exact List.isChain_cons_cons.mpr ⟨rfl, chain⟩
    · exact (prepend_last _ posts positive).trans last
  | load update tail ih =>
    obtain ⟨posts, positive, bound, chain, last⟩ := ih (update tape.head store) tape
    refine ⟨posts, positive, ?_, ?_, last⟩
    · change posts.length ≤ weight tail + 1
      omega
    · exact replace_first (TM0.step (TM1to0.tr machine))
        (entry machine tail (update tape.head store) tape)
        (entry machine (.load update tail) store tape) posts positive rfl chain
  | branch condition left right leftIH rightIH =>
    cases decision : condition tape.head store with
    | false =>
      obtain ⟨posts, positive, bound, chain, last⟩ := rightIH store tape
      have firstSame : TM0.step (TM1to0.tr machine) (entry machine (.branch condition left right) store tape) =
          TM0.step (TM1to0.tr machine) (entry machine right store tape) := by
        dsimp only [entry, TM0.step, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      refine ⟨posts, positive, ?_, ?_, ?_⟩
      · change posts.length ≤ weight left + weight right + 1
        omega
      · exact replace_first _ _ _ posts positive firstSame chain
      · change posts.getLast? = some (TM1to0.trCfg machine
          (cond (condition tape.head store) (TM1.stepAux left store tape) (TM1.stepAux right store tape)))
        rw [decision]
        exact last
    | true =>
      obtain ⟨posts, positive, bound, chain, last⟩ := leftIH store tape
      have firstSame : TM0.step (TM1to0.tr machine) (entry machine (.branch condition left right) store tape) =
          TM0.step (TM1to0.tr machine) (entry machine left store tape) := by
        dsimp only [entry, TM0.step, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      refine ⟨posts, positive, ?_, ?_, ?_⟩
      · change posts.length ≤ weight left + weight right + 1
        omega
      · exact replace_first _ _ _ posts positive firstSame chain
      · change posts.getLast? = some (TM1to0.trCfg machine
          (cond (condition tape.head store) (TM1.stepAux left store tape) (TM1.stepAux right store tape)))
        rw [decision]
        exact last

end PaperProofs.Common.Native.PSTRWordBool.StatementClock
