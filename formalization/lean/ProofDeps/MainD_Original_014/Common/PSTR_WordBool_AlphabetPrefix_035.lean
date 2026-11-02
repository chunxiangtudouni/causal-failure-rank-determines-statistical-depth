module

public import Common.PSTR_WordBool_AlphabetReadNet_034

/-! Physical displacement before the alphabet compiler's first write port,
and displacement of the real write/rewind continuation. Syntax radii are
fixed by source code before input; no elapsed-time radius is used. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AlphabetPrefix

open Turing StatementDisplacement AlphabetMotion AlphabetReadNet

variable {Γ Λ σ : Type*} [Inhabited Γ]

def motionRadius : TM1.Stmt Γ Λ σ → Nat
  | .move _ tail => motionRadius tail + 1
  | .write _ tail | .load _ tail => motionRadius tail
  | .branch _ yes no => motionRadius yes + motionRadius no
  | .goto _ | .halt => 0

def leadingMove : TM1.Stmt Γ Λ σ → σ → Tape Γ → Int
  | .move direction tail, store, tape => delta direction + leadingMove tail store (tape.move direction)
  | .write _ _, _, _ => 0
  | .load value tail, store, tape => leadingMove tail (value tape.head store) tape
  | .branch test yes no, store, tape =>
      cond (test tape.head store) (leadingMove yes store tape) (leadingMove no store tape)
  | .goto _, _, _ | .halt, _, _ => 0

theorem leading_bound (statement : TM1.Stmt Γ Λ σ) (store : σ) (tape : Tape Γ) :
    -(motionRadius statement : Int) ≤ leadingMove statement store tape ∧
      leadingMove statement store tape ≤ (motionRadius statement : Int) := by
  induction statement generalizing store tape with
  | move direction tail ih =>
    have bound := ih store (tape.move direction)
    cases direction <;> simp only [motionRadius, leadingMove, delta, Int.natCast_add,
      Int.natCast_one] <;> constructor <;> omega
  | write value tail =>
    simp only [motionRadius, leadingMove]
    constructor <;> omega
  | load value tail ih => exact ih (value tape.head store) tape
  | branch test yes no ihYes ihNo =>
    have yesBound := ihYes store tape
    have noBound := ihNo store tape
    cases choice : test tape.head store <;>
      simp only [motionRadius, leadingMove, choice, Bool.cond_false, Bool.cond_true,
        Int.natCast_add] <;> constructor <;> omega
  | goto target => simp only [motionRadius, leadingMove, Int.natCast_zero, neg_zero, le_refl, and_self]
  | halt => simp only [motionRadius, leadingMove, Int.natCast_zero, neg_zero, le_refl, and_self]

theorem net_bound (statement : TM1.Stmt Γ Λ σ) (store : σ) (tape : Tape Γ) :
    -(motionRadius statement : Int) ≤ netMove statement store tape ∧
      netMove statement store tape ≤ (motionRadius statement : Int) := by
  induction statement generalizing store tape with
  | move direction tail ih =>
    have bound := ih store (tape.move direction)
    cases direction <;> simp only [motionRadius, netMove, delta, Int.natCast_add,
      Int.natCast_one] <;> constructor <;> omega
  | write value tail ih => exact ih store (tape.write (value tape.head store))
  | load value tail ih => exact ih (value tape.head store) tape
  | branch test yes no ihYes ihNo =>
    have yesBound := ihYes store tape
    have noBound := ihNo store tape
    cases choice : test tape.head store <;>
      simp only [motionRadius, netMove, choice, Bool.cond_false, Bool.cond_true,
        Int.natCast_add] <;> constructor <;> omega
  | goto target => simp only [motionRadius, netMove, Int.natCast_zero, neg_zero, le_refl, and_self]
  | halt => simp only [motionRadius, netMove, Int.natCast_zero, neg_zero, le_refl, and_self]

variable {count : Nat} (encode : Γ → List.Vector Bool count)
    (decode : List.Vector Bool count → Γ)
    (pointed : encode default = List.Vector.replicate count false)
    (inverse : ∀ symbol, decode (encode symbol) = symbol)

include inverse

theorem normal_net (statement : TM1.Stmt Γ Λ σ) (store : σ) (tape : Tape Γ) :
    netMove (TM1to1.trNormal decode statement) store (TM1to1.trTape pointed tape) =
      (count : Int) * leadingMove statement store tape := by
  induction statement generalizing store tape with
  | move direction tail ih =>
    have moved : (Tape.move direction)^[count] (TM1to1.trTape pointed tape) =
        TM1to1.trTape pointed (tape.move direction) := by
      obtain ⟨left, right, rfl⟩ := tape.exists_mk'
      cases direction
      · simp only [TM1to1.trTape_mk', Tape.move_left_mk', TM1to1.trTape'_move_left pointed]
      · simp only [TM1to1.trTape_mk', Tape.move_right_mk', TM1to1.trTape'_move_right pointed]
    change netMove (TM1to1.move count direction (TM1to1.trNormal decode tail)) store
      (TM1to1.trTape pointed tape) = _
    unfold TM1to1.move
    rw [net_moves, moved, ih store (tape.move direction)]
    change (count : Int) * delta direction + (count : Int) * leadingMove tail store (tape.move direction) =
      (count : Int) * (delta direction + leadingMove tail store (tape.move direction))
    ring
  | write value tail =>
    change netMove (TM1to1.read decode (fun symbol =>
      .goto (fun _ memory => .write (value symbol memory) tail))) store
        (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    simp only [netMove, leadingMove, Int.mul_zero]
  | load value tail ih =>
    change netMove (TM1to1.read decode (fun symbol =>
      .load (fun _ memory => value symbol memory) (TM1to1.trNormal decode tail))) store
        (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    exact ih (value tape.head store) tape
  | branch test yes no ihYes ihNo =>
    change netMove (TM1to1.read decode (fun symbol =>
      .branch (fun _ memory => test symbol memory)
        (TM1to1.trNormal decode yes) (TM1to1.trNormal decode no))) store
      (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    simp only [netMove, leadingMove]
    cases choice : test tape.head store
    · simpa only [choice, Bool.cond_false] using ihNo store tape
    · simpa only [choice, Bool.cond_true] using ihYes store tape
  | goto target =>
    change netMove (TM1to1.read decode (fun symbol =>
      .goto (fun _ memory => .normal (target symbol memory)))) store
        (TM1to1.trTape pointed tape) = _
    rw [read_encoded_net encode decode pointed inverse]
    simp only [netMove, leadingMove, Int.mul_zero]
  | halt => simp only [TM1to1.trNormal, netMove, leadingMove, Int.mul_zero]

theorem write_continuation_net (machine : Λ → TM1.Stmt Γ Λ σ)
    (tail : TM1.Stmt Γ Λ σ) (store : σ) (new old : Γ) (left right : ListBlank Γ) :
    netMove (TM1to1.tr encode decode machine (.write new tail)) store
      (TM1to1.trTape' pointed left (right.cons old)) =
      (count : Int) * leadingMove tail store (Tape.mk' left (right.cons new)) := by
  have restored : (Tape.move .left)^[count]
      (TM1to1.trTape' pointed (left.cons new) right) =
      TM1to1.trTape' pointed left (right.cons new) := by
    simpa only [ListBlank.tail_cons, ListBlank.head_cons] using
      TM1to1.trTape'_move_left pointed (left.cons new) right
  have tailNet : netMove (TM1to1.trNormal decode tail) store
      (TM1to1.trTape' pointed left (right.cons new)) =
      (count : Int) * leadingMove tail store (Tape.mk' left (right.cons new)) := by
    simpa only [TM1to1.trTape_mk'] using normal_net encode decode pointed inverse
      tail store (Tape.mk' left (right.cons new))
  simp only [TM1to1.tr, TM1to1.move]
  rw [net_write_encoded encode pointed, net_moves, restored, tailNet]
  simp only [delta]
  ring

end PaperProofs.Common.Native.PSTRWordBool.AlphabetPrefix
