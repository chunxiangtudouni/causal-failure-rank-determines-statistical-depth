module
public import PaperProofs.Structure.PA17_UniformGenerator_035b

/-! Symbolic original instructions for actual dimension-only generation.
Only constant immediates are expressions; ordinary operands remain the
existing ISA's registers. Encoding is the existing exact five-word encoding. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b

inductive OpExpr where
  | constant (target : Register) (value : Expr)
  | literal (op : Op)

def OpExpr.eval (rom : PhysicalROM) (environment : Nat → Nat) : OpExpr → Op
  | .constant target value => .base (.constant target (value.eval rom environment))
  | .literal op => op

def OpExpr.words : OpExpr → List Expr
  | .constant target value => [.constant 0, .constant target.word, value, .constant 0, .constant 0]
  | .literal op => op.encodeWords.toArray.toList.map Expr.constant

theorem OpExpr.words_length (op : OpExpr) : op.words.length = 5 := by
  cases op <;> simp [OpExpr.words]

theorem OpExpr.words_eval (op : OpExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (op.words.map (Expr.eval rom environment)) = (op.eval rom environment).encodeWords.toArray.toList := by
  cases op with
  | constant target value =>
    simp [OpExpr.words, OpExpr.eval, Expr.eval, Op.encodeWords, Instruction.encodeWords]
  | literal op =>
    simp only [OpExpr.words, OpExpr.eval, List.map_map]
    change List.map id _ = _
    exact List.map_id _

def expressions (ops : List OpExpr) : List Expr := ops.flatMap OpExpr.words

def instructions (rom : PhysicalROM) (environment : Nat → Nat) (ops : List OpExpr) : List Op :=
  ops.map (OpExpr.eval rom environment)

theorem expressions_length (ops : List OpExpr) : (expressions ops).length = 5 * ops.length := by
  induction ops with
  | nil => rfl
  | cons op later ih =>
    simp only [expressions, List.flatMap_cons, List.length_append, OpExpr.words_length,
      List.length_cons] at *
    omega

theorem expressions_eval (ops : List OpExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (expressions ops).map (Expr.eval rom environment) = IndexedClosureRAM.programWords (instructions rom environment ops) := by
  induction ops with
  | nil => rfl
  | cons op later ih =>
    simp only [expressions, instructions, List.flatMap_cons, List.map_append, List.map_cons,
      IndexedClosureRAM.programWords, List.flatMap_cons, OpExpr.words_eval] at *
    exact congrArg ((op.eval rom environment).encodeWords.toArray.toList ++ ·) ih

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
