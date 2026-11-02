module

public import Common.PSTR_WordBool_StatementClock_002

/-! Exact native displacement of a statement chunk. The final state is excluded
from the displacement sum: its next instruction belongs to the next chunk.
These are proof coordinates, never additional runtime control or input fields. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.StatementDisplacement

open Turing StatementClock

variable {Λ σ : Type*}

def delta : Dir → Int
  | .left => -1
  | .right => 1

def netMove {Γ : Type*} [Inhabited Γ] : TM1.Stmt Γ Λ σ → σ → Tape Γ → Int
  | .move direction tail, store, tape => delta direction + netMove tail store (tape.move direction)
  | .write value tail, store, tape => netMove tail store (tape.write (value tape.head store))
  | .load value tail, store, tape => netMove tail (value tape.head store) tape
  | .branch test yes no, store, tape =>
      cond (test tape.head store) (netMove yes store tape) (netMove no store tape)
  | .goto _, _, _ | .halt, _, _ => 0

variable [Inhabited Λ] [Inhabited σ]

def shift (machine : Λ → TM1.Stmt Bool Λ σ) (state : NativeState machine) : Int :=
  match (TM1to0.tr machine) state.q state.Tape.head with
  | some (_, .move .left) => -1
  | some (_, .move .right) => 1
  | _ => 0

def traceMove (machine : Λ → TM1.Stmt Bool Λ σ) (trace : List (NativeState machine)) : Int :=
  (trace.dropLast.map (shift machine)).sum

theorem move_cons (machine : Λ → TM1.Stmt Bool Λ σ) (first : NativeState machine)
    (posts : List (NativeState machine)) (positive : 1 ≤ posts.length) :
    traceMove machine (first :: posts) = shift machine first + traceMove machine posts := by
  cases posts with
  | nil => simp at positive
  | cons head tail =>
    simp only [traceMove, List.dropLast_cons_cons, List.map_cons, List.sum_cons]

theorem replace_move (machine : Λ → TM1.Stmt Bool Λ σ) (original replacement : NativeState machine)
    (posts : List (NativeState machine)) (positive : 1 ≤ posts.length)
    (same : shift machine replacement = shift machine original) :
    traceMove machine (replacement :: posts) = traceMove machine (original :: posts) := by
  rw [move_cons machine replacement posts positive, move_cons machine original posts positive, same]

theorem statement_chunk (machine : Λ → TM1.Stmt Bool Λ σ)
    (statement : TM1.Stmt Bool Λ σ) (store : σ) (tape : Tape Bool) :
    ∃ posts : List (NativeState machine),
      1 ≤ posts.length ∧ posts.length ≤ weight statement ∧
      (entry machine statement store tape :: posts).IsChain
        (fun before after => TM0.step (TM1to0.tr machine) before = some after) ∧
      posts.getLast? = some (TM1to0.trCfg machine (TM1.stepAux statement store tape)) ∧
      traceMove machine (entry machine statement store tape :: posts) = netMove statement store tape := by
  induction statement generalizing store tape with
  | halt =>
    let final := TM1to0.trCfg machine (TM1.stepAux .halt store tape)
    have first : TM0.step (TM1to0.tr machine) (entry machine .halt store tape) = some final := by
      change (some ⟨(none, store), tape.write tape.head⟩ : Option (NativeState machine)) = some final
      rw [Tape.write_self]
      rfl
    refine ⟨[final], le_rfl, le_rfl, List.isChain_cons_cons.mpr ⟨first, List.isChain_singleton _⟩, rfl, ?_⟩
    rfl
  | goto target =>
    let final := TM1to0.trCfg machine (TM1.stepAux (.goto target) store tape)
    have first : TM0.step (TM1to0.tr machine) (entry machine (.goto target) store tape) = some final := by
      change (some ⟨(some (machine (target tape.head store)), store), tape.write tape.head⟩ :
        Option (NativeState machine)) = some final
      rw [Tape.write_self]
      rfl
    refine ⟨[final], le_rfl, le_rfl, List.isChain_cons_cons.mpr ⟨first, List.isChain_singleton _⟩, rfl, ?_⟩
    rfl
  | move direction tail ih =>
    obtain ⟨posts, positive, bound, chain, last, movement⟩ := ih store (tape.move direction)
    refine ⟨entry machine tail store (tape.move direction) :: posts, by simp,
      Nat.succ_le_succ bound, List.isChain_cons_cons.mpr ⟨rfl, chain⟩,
      (prepend_last _ posts positive).trans last, ?_⟩
    rw [move_cons machine _ _ (by simp), movement]
    cases direction <;> rfl
  | write value tail ih =>
    obtain ⟨posts, positive, bound, chain, last, movement⟩ := ih store (tape.write (value tape.head store))
    refine ⟨entry machine tail store (tape.write (value tape.head store)) :: posts, by simp,
      Nat.succ_le_succ bound, List.isChain_cons_cons.mpr ⟨rfl, chain⟩,
      (prepend_last _ posts positive).trans last, ?_⟩
    rw [move_cons machine _ _ (by simp), movement]
    change 0 + netMove tail store (tape.write (value tape.head store)) = _
    exact Int.zero_add _
  | load value tail ih =>
    obtain ⟨posts, positive, bound, chain, last, movement⟩ := ih (value tape.head store) tape
    refine ⟨posts, positive, ?_, ?_, last, ?_⟩
    · change posts.length ≤ weight tail + 1
      omega
    · exact replace_first (TM0.step (TM1to0.tr machine))
        (entry machine tail (value tape.head store) tape)
        (entry machine (.load value tail) store tape) posts positive rfl chain
    · exact (replace_move machine (entry machine tail (value tape.head store) tape)
        (entry machine (.load value tail) store tape) posts positive rfl).trans movement
  | branch test yes no yesIH noIH =>
    cases decision : test tape.head store with
    | false =>
      obtain ⟨posts, positive, bound, chain, last, movement⟩ := noIH store tape
      have firstSame : TM0.step (TM1to0.tr machine) (entry machine (.branch test yes no) store tape) =
          TM0.step (TM1to0.tr machine) (entry machine no store tape) := by
        dsimp only [entry, TM0.step, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      have shiftSame : shift machine (entry machine (.branch test yes no) store tape) =
          shift machine (entry machine no store tape) := by
        dsimp only [shift, entry, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      refine ⟨posts, positive, ?_, replace_first _ _ _ posts positive firstSame chain, ?_, ?_⟩
      · change posts.length ≤ weight yes + weight no + 1
        omega
      · change posts.getLast? = some (TM1to0.trCfg machine
          (cond (test tape.head store) (TM1.stepAux yes store tape) (TM1.stepAux no store tape)))
        rw [decision]
        exact last
      · change traceMove machine (entry machine (.branch test yes no) store tape :: posts) =
          cond (test tape.head store) (netMove yes store tape) (netMove no store tape)
        rw [decision]
        exact (replace_move machine _ _ posts positive shiftSame).trans movement
    | true =>
      obtain ⟨posts, positive, bound, chain, last, movement⟩ := yesIH store tape
      have firstSame : TM0.step (TM1to0.tr machine) (entry machine (.branch test yes no) store tape) =
          TM0.step (TM1to0.tr machine) (entry machine yes store tape) := by
        dsimp only [entry, TM0.step, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      have shiftSame : shift machine (entry machine (.branch test yes no) store tape) =
          shift machine (entry machine yes store tape) := by
        dsimp only [shift, entry, TM1to0.tr, TM1to0.trAux]
        rw [decision]
        rfl
      refine ⟨posts, positive, ?_, replace_first _ _ _ posts positive firstSame chain, ?_, ?_⟩
      · change posts.length ≤ weight yes + weight no + 1
        omega
      · change posts.getLast? = some (TM1to0.trCfg machine
          (cond (test tape.head store) (TM1.stepAux yes store tape) (TM1.stepAux no store tape)))
        rw [decision]
        exact last
      · change traceMove machine (entry machine (.branch test yes no) store tape :: posts) =
          cond (test tape.head store) (netMove yes store tape) (netMove no store tape)
        rw [decision]
        exact (replace_move machine _ _ posts positive shiftSame).trans movement

end PaperProofs.Common.Native.PSTRWordBool.StatementDisplacement
