module

public import Structure.PSTR_BuildLower_BankFrame_017
public import Structure.PSTR_BuildLower_FixedExpr_010
public import Structure.PSTR_HD_WordSegments_014

/-! Direct Word expression semantics. Every ISA truncation is retained;
only separation of finitely many static bank offsets is used. No Nat
RegistersFit premise for a whole packed body or complete AST is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

def binaryWordEval (operation : Binary) (left right : BitVec bits) : BitVec bits :=
  match operation with
  | .add => left + right
  | .subtract => BitVec.ofNat bits (left.toNat - right.toNat)
  | .minimum => if left.toNat ≤ right.toNat then left else right
  | .multiply => packingArithmetic .multiply left right
  | .divide => packingArithmetic .divide left right
  | .bitAnd => packingArithmetic .bitAnd left right
  | .bitOr => packingArithmetic .bitOr left right
  | .shiftLeft => packingArithmetic .shiftLeft left right
  | .shiftRight => packingArithmetic .shiftRight left right

def exprWordEval (rom : PhysicalROM) (heap : Nat → BitVec bits) : Expr → BitVec bits
  | .constant value => BitVec.ofNat bits value
  | .cell address => heap address
  | .input address => BitVec.ofNat bits ((rom.words .input).getD (BitVec.ofNat bits address).toNat 0)
  | .binary operation left right => binaryWordEval operation (exprWordEval rom heap left) (exprWordEval rom heap right)

theorem exprWordEval_congr (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expr.Below stack) (heap heap' : Nat → BitVec bits)
    (hh : ∀ address < stack, heap' address = heap address) :
    exprWordEval rom heap' expr = exprWordEval rom heap expr := by
  induction expr with
  | constant value => rfl
  | cell address => exact hh address hf
  | input address => rfl
  | binary operation left right ihl ihr =>
    simp only [exprWordEval, ihl hf.1, ihr hf.2]

private theorem bank_offset_ne (base : BitVec bits) (left right : Nat)
    (hl : left < 2 ^ bits) (hr : right < 2 ^ bits) (hne : left ≠ right) :
    base + BitVec.ofNat bits left ≠ base + BitVec.ofNat bits right := by
  intro hh
  have he := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp hh)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at he
  exact hne he

theorem bankCompile_word_read_below (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (state : WordState bits) (address : Nat) (ha : address < stack)
    (ht : stack + expr.size ≤ 2 ^ bits) :
    (executeOps rom (bankCompile stack expr) state).heap
        (state.register .address + BitVec.ofNat bits address) =
      state.heap (state.register .address + BitVec.ofNat bits address) := by
  have hh := (bankCompile_word_frame expr rom stack).2 state
    (state.register .address + BitVec.ofNat bits address) (by
      intro offset hlo hhi
      exact bank_offset_ne _ _ _ (by omega) (by omega) (by omega)) (bankCompile stack expr).length
  simpa only [List.take_length] using hh

private theorem bankCompile_word_base (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (state : WordState bits) :
    (executeOps rom (bankCompile stack expr) state).register .address = state.register .address := by
  have hh := (bankCompile_word_frame expr rom stack).1 state (bankCompile stack expr).length
  simpa only [List.take_length] using hh

private theorem bankWrite_word_base (rom : PhysicalROM) (stack : Nat) (state : WordState bits) :
    (executeOps rom (relativeWrite stack) state).register .address = state.register .address := rfl

private theorem bankFinish_word_value (rom : PhysicalROM) (stack : Nat) (operation : Binary)
    (state : WordState bits) :
    (executeOps rom (bankFinish stack operation) state).register .value =
      binaryWordEval operation (state.heap (state.register .address + BitVec.ofNat bits stack))
        (state.register .value) := by
  cases operation <;> rfl

private theorem bankFinish_word_base (rom : PhysicalROM) (stack : Nat) (operation : Binary)
    (state : WordState bits) :
    (executeOps rom (bankFinish stack operation) state).register .address = state.register .address := by
  cases operation <;> rfl

/-- Actual compiled Word result, including modular arithmetic and shifts.
The numeric premise separates static offset addresses; it is independent of
all Expr values, and does not bound or replace any runtime intermediate. -/
theorem bankCompile_word_value (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expr.Below stack) (ht : stack + expr.size ≤ 2 ^ bits) (state : WordState bits) :
    (executeOps rom (bankCompile stack expr) state).register .value =
      exprWordEval rom (fun address => state.heap (state.register .address + BitVec.ofNat bits address)) expr := by
  induction expr generalizing stack state with
  | constant value => rfl
  | cell address => exact relativeRead_value rom address .value state
  | input address => rfl
  | binary operation left right ihl ihr =>
    let a := executeOps rom (bankCompile stack left) state
    let b := executeOps rom (relativeWrite stack) a
    let c := executeOps rom (bankCompile (stack + 1) right) b
    have hsize : (Expr.binary operation left right).size = left.size + right.size + 1 := rfl
    rw [hsize] at ht
    have hl := ihl stack hf.1 (by omega) state
    have habase : a.register .address = state.register .address := bankCompile_word_base left rom stack state
    have hbbase : b.register .address = state.register .address := (bankWrite_word_base rom stack a).trans habase
    have hr := ihr (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hf.2) (by omega) b
    have hcbase : c.register .address = state.register .address :=
      (bankCompile_word_base right rom (stack + 1) b).trans hbbase
    have hbframe (address : Nat) (ha : address < stack) :
        b.heap (state.register .address + BitVec.ofNat bits address) =
          state.heap (state.register .address + BitVec.ofNat bits address) := by
      change (executeOps rom (relativeWrite stack) a).heap _ = _
      rw [relativeWrite_heap, habase, Function.update_of_ne
        (bank_offset_ne _ _ _ (by omega) (by omega) (by omega))]
      exact bankCompile_word_read_below left rom stack state address ha (by omega)
    have heval := exprWordEval_congr right rom stack hf.2
      (fun address => state.heap (state.register .address + BitVec.ofNat bits address))
      (fun address => b.heap (b.register .address + BitVec.ofNat bits address)) (by
        intro address ha
        rw [hbbase]
        exact hbframe address ha)
    have hstack : c.heap (state.register .address + BitVec.ofNat bits stack) =
        exprWordEval rom (fun address => state.heap (state.register .address + BitVec.ofNat bits address)) left := by
      have hh := bankCompile_word_read_below right rom (stack + 1) b stack (by omega) (by omega)
      rw [hbbase] at hh
      rw [hh]
      change (executeOps rom (relativeWrite stack) a).heap _ = _
      rw [relativeWrite_heap, habase, Function.update_self]
      exact hl
    dsimp only [bankCompile]
    rw [executeOps_append, executeOps_append, executeOps_append]
    rw [bankFinish_word_value, hcbase, hstack, hr, heval]
    rfl

theorem bankCompile_word_run (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (left right : List PackingOp) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ bankCompile stack expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ bankCompile stack expr ++ right).length)) :
    packingRun rom (left ++ bankCompile stack expr ++ right) (bankCompile stack expr).length state =
      executeOps rom (bankCompile stack expr) state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append]; omega)
    (PA17UniformGenerator035a.segment_index left (bankCompile stack expr) right)
    (bankCompile_noJump expr stack) hcode hpcfit state hpc ha

theorem bankCompile_word_actual_value (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expr.Below stack) (ht : stack + expr.size ≤ 2 ^ bits)
    (left right : List PackingOp) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ bankCompile stack expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ bankCompile stack expr ++ right).length)) :
    ((packingRun rom (left ++ bankCompile stack expr ++ right) (bankCompile stack expr).length state).register .value) =
      exprWordEval rom (fun address => state.heap (state.register .address + BitVec.ofNat bits address)) expr := by
  rw [bankCompile_word_run expr rom stack left right state hpc ha hcode hpcfit]
  exact bankCompile_word_value expr rom stack hf ht state

end PaperProofs.Structure.LaminarTree.PSTRBuildLower

