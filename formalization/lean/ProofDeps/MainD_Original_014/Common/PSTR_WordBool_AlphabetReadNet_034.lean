module

public import Common.PSTR_WordBool_AlphabetMotion_033
public import Mathlib.Tactic.Ring

/-! Actual read/rewind movement and the no-write part of alphabet compilation.
All helper widths are compile-time alphabet-code widths. No raw endpoint,
runtime word width or original caller certificate is introduced. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AlphabetReadNet

open Turing StatementDisplacement AlphabetMotion

variable {Γ Λ σ : Type*}

def readBits : (count : Nat) → Tape Bool → List.Vector Bool count
  | 0, _ => List.Vector.nil
  | count + 1, tape => List.Vector.cons tape.head (readBits count (tape.move .right))

theorem readAux_steps (count : Nat)
    (continuation : List.Vector Bool count → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (tape : Tape Bool) :
    TM1.stepAux (TM1to1.readAux count continuation) store tape =
      TM1.stepAux (continuation (readBits count tape)) store ((Tape.move .right)^[count] tape) := by
  induction count generalizing tape with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    simp only [TM1to1.readAux, TM1.stepAux, readBits]
    cases bit : tape.head
    · simpa only [bit, Bool.cond_false] using
        ih (fun rest => continuation (List.Vector.cons false rest)) (tape.move .right)
    · simpa only [bit, Bool.cond_true] using
        ih (fun rest => continuation (List.Vector.cons true rest)) (tape.move .right)

theorem readAux_net (count : Nat)
    (continuation : List.Vector Bool count → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (tape : Tape Bool) :
    netMove (TM1to1.readAux count continuation) store tape = (count : Int) +
      netMove (continuation (readBits count tape)) store ((Tape.move .right)^[count] tape) := by
  induction count generalizing tape with
  | zero => simp only [TM1to1.readAux, readBits, Function.iterate_zero_apply, Int.natCast_zero, Int.zero_add]
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    simp only [TM1to1.readAux, netMove, readBits, delta]
    cases bit : tape.head
    · simp only [Bool.cond_false]
      rw [ih]
      omega
    · simp only [Bool.cond_true]
      rw [ih]
      omega

theorem read_steps {count : Nat} (decode : List.Vector Bool count → Γ)
    (continuation : Γ → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ) (store : σ) (tape : Tape Bool) :
    TM1.stepAux (TM1to1.read decode continuation) store tape =
      TM1.stepAux (continuation (decode (readBits count tape))) store tape := by
  simp only [TM1to1.read]
  rw [readAux_steps, TM1to1.stepAux_move, right_left]

theorem read_net {count : Nat} (decode : List.Vector Bool count → Γ)
    (continuation : Γ → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ) (store : σ) (tape : Tape Bool) :
    netMove (TM1to1.read decode continuation) store tape =
      netMove (continuation (decode (readBits count tape))) store tape := by
  simp only [TM1to1.read]
  rw [readAux_net]
  unfold TM1to1.move
  rw [net_moves, right_left]
  dsimp only [delta]
  omega

variable [Inhabited Γ] {count : Nat} (encode : Γ → List.Vector Bool count)
    (decode : List.Vector Bool count → Γ)
    (pointed : encode default = List.Vector.replicate count false)
    (inverse : ∀ symbol, decode (encode symbol) = symbol)

include inverse

theorem decoded_read (left right : ListBlank Γ) :
    decode (readBits count (TM1to1.trTape' pointed left right)) = right.head := by
  let probe : Γ → TM1.Stmt Bool (TM1to1.Λ' Γ Unit Unit) Unit :=
    fun symbol => .goto (fun _ _ => .write symbol .halt)
  have raw := read_steps decode probe () (TM1to1.trTape' pointed left right)
  have actual := TM1to1.stepAux_read decode pointed inverse probe () left right
  have labels := congrArg
    (fun state : TM1.Cfg Bool (TM1to1.Λ' Γ Unit Unit) Unit => state.l) (raw.symm.trans actual)
  change some (TM1to1.Λ'.write (decode (readBits count (TM1to1.trTape' pointed left right))) .halt) =
    some (TM1to1.Λ'.write right.head .halt) at labels
  exact (TM1to1.Λ'.write.inj (Option.some.inj labels)).1

theorem read_encoded_net (continuation : Γ → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (tape : Tape Γ) :
    netMove (TM1to1.read decode continuation) store (TM1to1.trTape pointed tape) =
      netMove (continuation tape.head) store (TM1to1.trTape pointed tape) := by
  obtain ⟨left, right, rfl⟩ := tape.exists_mk'
  rw [TM1to1.trTape_mk', read_net, decoded_read encode decode pointed inverse, Tape.mk'_head]

theorem no_write_net (statement : TM1.Stmt Γ Λ σ) (store : σ) (tape : Tape Γ)
    (noWrites : AlphabetClock.writes statement = 0) :
    netMove (TM1to1.trNormal decode statement) store (TM1to1.trTape pointed tape) =
      (count : Int) * netMove statement store tape := by
  induction statement generalizing store tape with
  | move direction tail ih =>
    have tailNo : AlphabetClock.writes tail = 0 := noWrites
    have moved : (Tape.move direction)^[count] (TM1to1.trTape pointed tape) =
        TM1to1.trTape pointed (tape.move direction) := by
      obtain ⟨left, right, rfl⟩ := tape.exists_mk'
      cases direction
      · simp only [TM1to1.trTape_mk', Tape.move_left_mk', TM1to1.trTape'_move_left pointed]
      · simp only [TM1to1.trTape_mk', Tape.move_right_mk', TM1to1.trTape'_move_right pointed]
    change netMove (TM1to1.move count direction (TM1to1.trNormal decode tail)) store
      (TM1to1.trTape pointed tape) = _
    unfold TM1to1.move
    rw [net_moves, moved, ih store (tape.move direction) tailNo]
    change (count : Int) * delta direction + (count : Int) * netMove tail store (tape.move direction) =
      (count : Int) * (delta direction + netMove tail store (tape.move direction))
    ring
  | write value tail =>
    change AlphabetClock.writes tail + 1 = 0 at noWrites
    omega
  | load value tail ih =>
    have tailNo : AlphabetClock.writes tail = 0 := noWrites
    change netMove (TM1to1.read decode (fun symbol =>
      .load (fun _ memory => value symbol memory) (TM1to1.trNormal decode tail))) store
        (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    exact ih (value tape.head store) tape tailNo
  | branch test yes no ihYes ihNo =>
    have zeroYes : AlphabetClock.writes yes = 0 := by
      change AlphabetClock.writes yes + AlphabetClock.writes no = 0 at noWrites
      omega
    have zeroNo : AlphabetClock.writes no = 0 := by
      change AlphabetClock.writes yes + AlphabetClock.writes no = 0 at noWrites
      omega
    change netMove (TM1to1.read decode (fun symbol =>
      .branch (fun _ memory => test symbol memory)
        (TM1to1.trNormal decode yes) (TM1to1.trNormal decode no))) store
      (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    simp only [netMove]
    cases choice : test tape.head store
    · simpa only [choice, Bool.cond_false] using ihNo store tape zeroNo
    · simpa only [choice, Bool.cond_true] using ihYes store tape zeroYes
  | goto target =>
    change netMove (TM1to1.read decode (fun symbol =>
      .goto (fun _ memory => .normal (target symbol memory)))) store
        (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    simp only [netMove, Int.mul_zero]
  | halt => simp only [TM1to1.trNormal, netMove, Int.mul_zero]

end PaperProofs.Common.Native.PSTRWordBool.AlphabetReadNet
