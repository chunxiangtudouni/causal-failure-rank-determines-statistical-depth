module

public import Common.PSTR_WordBool_StatementSpan_027
public import Common.PSTR_WordBool_AlphabetClock_005

/-! Exact net movement of the alphabet compiler's actual primitive programs.
The width below is the fixed alphabet-code width, never runtime Word width.
Tape equalities and net displacements are proved separately and coupled. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AlphabetMotion

open Turing StatementDisplacement

variable {Γ Λ σ : Type*}

theorem net_moves (count : Nat) (direction : Dir)
    (tail : TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ) (store : σ) (tape : Tape Bool) :
    netMove ((TM1.Stmt.move direction)^[count] tail) store tape =
      (count : Int) * delta direction + netMove tail store ((Tape.move direction)^[count] tape) := by
  induction count generalizing tail tape with
  | zero => simp only [Function.iterate_zero_apply, Int.natCast_zero, Int.zero_mul, Int.zero_add]
  | succ count ih =>
    rw [Function.iterate_succ', Function.iterate_succ]
    simp only [Function.comp_apply, netMove]
    rw [ih]
    cases direction <;> dsimp only [delta] <;> omega

theorem right_left (count : Nat) (tape : Tape Bool) :
    (Tape.move .left)^[count] ((Tape.move .right)^[count] tape) = tape := by
  induction count generalizing tape with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', Tape.move_right_left, ih]

def written : List Bool → Tape Bool → Tape Bool
  | [], tape => tape
  | bit :: rest, tape => written rest ((tape.write bit).move .right)

theorem write_steps (bits : List Bool) (tail : TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (tape : Tape Bool) :
    TM1.stepAux (TM1to1.write bits tail) store tape = TM1.stepAux tail store (written bits tape) := by
  induction bits generalizing tape with
  | nil => rfl
  | cons bit rest ih => exact ih ((tape.write bit).move .right)

theorem net_write (bits : List Bool) (tail : TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (tape : Tape Bool) :
    netMove (TM1to1.write bits tail) store tape =
      (bits.length : Int) + netMove tail store (written bits tape) := by
  induction bits generalizing tape with
  | nil => simp only [TM1to1.write, written, List.length_nil, Int.natCast_zero, Int.zero_add]
  | cons bit rest ih =>
    simp only [TM1to1.write, netMove, delta, written, List.length_cons]
    rw [ih]
    omega

variable [Inhabited Γ] {count : Nat} (encode : Γ → List.Vector Bool count)
    (pointed : encode default = List.Vector.replicate count false)

theorem written_encoded (new old : Γ) (left right : ListBlank Γ) :
    written (encode new).toList (TM1to1.trTape' pointed left (right.cons old)) =
      TM1to1.trTape' pointed (left.cons new) right := by
  have actual := TM1to1.stepAux_write pointed
    (TM1.Stmt.halt : TM1.Stmt Bool (TM1to1.Λ' Γ Unit Unit) Unit) () new old left right
  rw [write_steps] at actual
  exact congrArg (fun state : TM1.Cfg Bool (TM1to1.Λ' Γ Unit Unit) Unit => state.Tape) actual

theorem net_write_encoded (tail : TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ)
    (store : σ) (new old : Γ) (left right : ListBlank Γ) :
    netMove (TM1to1.write (encode new).toList tail) store
      (TM1to1.trTape' pointed left (right.cons old)) =
      (count : Int) + netMove tail store (TM1to1.trTape' pointed (left.cons new) right) := by
  rw [net_write, List.Vector.toList_length, written_encoded encode pointed]

end PaperProofs.Common.Native.PSTRWordBool.AlphabetMotion
