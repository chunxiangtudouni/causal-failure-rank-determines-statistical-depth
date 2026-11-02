module

public import Structure.PSTR_BuildLower_Control_001

/-! The original Expr compiler writes only its real temporary stack, at every
instruction prefix. Input localization is parameterized by actual control-bank
addresses: this file chooses no physical dimension or cache layout. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b

variable {bits : Nat}

def WordPrefixFrame (rom : PhysicalROM) (code : List PackingOp)
    (point : BitVec bits) : Prop :=
  ∀ (state : WordState bits) (count : Nat),
    (executeOps rom (code.take count) state).heap point = state.heap point

theorem wordPrefixFrame_append (rom : PhysicalROM) (left right : List PackingOp)
    (point : BitVec bits) (hl : WordPrefixFrame rom left point)
    (hr : WordPrefixFrame rom right point) : WordPrefixFrame rom (left ++ right) point := by
  intro state count
  rw [List.take_append, executeOps_append, hr, hl]

theorem wordPrefixFrame_spill (rom : PhysicalROM) (stack : Nat) (point : BitVec bits)
    (hne : point ≠ BitVec.ofNat bits stack) : WordPrefixFrame rom (spill stack) point := by
  intro state count
  cases count with
  | zero => rfl
  | succ count => cases count <;>
      simp [spill, executeOps, packingExecuteOp, wordOp, wordInstruction,
        Function.update_of_ne hne]

theorem wordPrefixFrame_finish (rom : PhysicalROM) (stack : Nat) (op : Binary)
    (point : BitVec bits) : WordPrefixFrame rom (finish stack op) point := by
  intro state count
  cases count with
  | zero => rfl
  | succ count => cases count with
    | zero => rfl
    | succ count => cases count <;> cases op <;>
        simp [finish, Binary.instruction, executeOps, packingExecuteOp, wordOp, wordInstruction]

/-- No preservation assumption on target data, virtual registers, or cache is
needed: only the enumerated physical temporary words can be written. This
formulation remains valid at small word widths where addresses can alias. -/
theorem expr_compile_word_prefix_frame (expr : Expr) (rom : PhysicalROM)
    (stack : Nat) (point : BitVec bits)
    (outside : ∀ address, stack ≤ address → address < stack + expr.size →
      point ≠ BitVec.ofNat bits address) :
    WordPrefixFrame rom (expr.compile stack) point := by
  induction expr generalizing stack with
  | constant value =>
    intro state count
    cases count <;> simp [Expr.compile, executeOps, packingExecuteOp, wordOp, wordInstruction]
  | cell address =>
    intro state count
    cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [Expr.compile, executeOps, packingExecuteOp, wordOp, wordInstruction]
  | input address =>
    intro state count
    cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [Expr.compile, executeOps, packingExecuteOp, wordOp, wordInstruction]
  | binary op left right ihl ihr =>
    simp only [Expr.compile]
    apply wordPrefixFrame_append rom _ _ point
    · apply ihl
      intro address hlo hhi
      apply outside address hlo
      simp only [Expr.size] at *
      omega
    · apply wordPrefixFrame_append rom _ _ point
      · apply wordPrefixFrame_spill
        apply outside stack le_rfl
        simp only [Expr.size]
        omega
      · apply wordPrefixFrame_append rom _ _ point
        · apply ihr
          intro address hlo hhi
          apply outside address (by omega)
          simp only [Expr.size] at *
          omega
        · exact wordPrefixFrame_finish rom stack op point

def exprInputsBelow (bound : Nat) : Expr → Prop
  | .constant _ | .cell _ => True
  | .input address => address < bound
  | .binary _ left right => exprInputsBelow bound left ∧ exprInputsBelow bound right

def localizeExpr (dimensions : Nat → Nat) : Expr → Expr
  | .constant value => .constant value
  | .cell address => .cell address
  | .input address => .cell (dimensions address)
  | .binary op left right => .binary op (localizeExpr dimensions left) (localizeExpr dimensions right)

theorem expr_localize_size (expr : Expr) (dimensions : Nat → Nat) :
    (localizeExpr dimensions expr).size = expr.size := by
  induction expr with
  | constant value => rfl
  | cell address => rfl
  | input address => rfl
  | binary op left right ihl ihr => simp only [localizeExpr, Expr.size, ihl, ihr]

theorem expr_localize_eval (expr : Expr) (dimensions : Nat → Nat) (bound : Nat)
    (hb : exprInputsBelow bound expr) (source physical : PhysicalROM) (heap : Nat → Nat)
    (hreal : ∀ address < bound, heap (dimensions address) = source.semantic.read .input address) :
    (localizeExpr dimensions expr).eval physical heap = expr.eval source heap := by
  induction expr with
  | constant value => rfl
  | cell address => rfl
  | input address => exact hreal address hb
  | binary op left right ihl ihr =>
    simp only [localizeExpr, Expr.eval, ihl hb.1, ihr hb.2]

theorem expr_localize_below (expr : Expr) (dimensions : Nat → Nat) (bound stack : Nat)
    (hb : exprInputsBelow bound expr) (hf : expr.Below stack)
    (hd : ∀ address < bound, dimensions address < stack) :
    (localizeExpr dimensions expr).Below stack := by
  induction expr with
  | constant value => trivial
  | cell address => exact hf
  | input address => exact hd address hb
  | binary op left right ihl ihr => exact ⟨ihl hb.1 hf.1, ihr hb.2 hf.2⟩

/-- The reused compiler computes a dynamic immediate from actual control cells.
No dimension-only replacement ROM is read by this execution. -/
theorem localized_compile_value (expr : Expr) (dimensions : Nat → Nat) (bound stack : Nat)
    (hb : exprInputsBelow bound expr) (hf : expr.Below stack)
    (hd : ∀ address < bound, dimensions address < stack)
    (source physical : PhysicalROM) (state : NatState)
    (hreal : ∀ address < bound, state.heap (dimensions address) = source.semantic.read .input address) :
    (runOps physical ((localizeExpr dimensions expr).compile stack) state).register .value =
      expr.eval source state.heap := by
  rw [(Expr.compile_correct (localizeExpr dimensions expr) physical stack
    (expr_localize_below expr dimensions bound stack hb hf hd) state).1]
  exact expr_localize_eval expr dimensions bound hb source physical state.heap hreal

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
