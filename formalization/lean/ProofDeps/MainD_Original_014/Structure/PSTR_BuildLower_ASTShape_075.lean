module

public import Structure.PSTR_BuildLower_OpExprRun_074

/-! Static certificates for the one original typed AST. These are syntax
facts, used to discharge the local compiler's expression/lexical hypotheses.
They contain no execution, output, capacity or runtime-cost assumption. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTShape
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041

def opCheck : OpExpr → Bool
  | .constant _ expr => decide (expr.size ≤ 29 ∧ expressionCellLimit expr ≤ 21 ∧ expressionInputLimit expr ≤ 3)
  | .literal _ => true

theorem op_sound (op : OpExpr) (hc : opCheck op = true) : SourceRep.OpExprShape op := by
  cases op with
  | constant target expr =>
    change expr.size ≤ 29 ∧ expressionCellLimit expr ≤ 21 ∧ expressionInputLimit expr ≤ 3
    exact of_decide_eq_true hc
  | literal original => trivial

def Shape : Program → Prop
  | .code ops => ∀ op ∈ ops, SourceRep.OpExprShape op
  | .append first second => Shape first ∧ Shape second
  | .repeat counter bound body => counter < 21 ∧ bound.size ≤ 29 ∧
      expressionCellLimit bound = 0 ∧ expressionInputLimit bound ≤ 3 ∧ Shape body

def check : Program → Bool
  | .code ops => ops.all opCheck
  | .append first second => check first && check second
  | .repeat counter bound body =>
      decide (counter < 21 ∧ bound.size ≤ 29 ∧ expressionCellLimit bound = 0 ∧ expressionInputLimit bound ≤ 3) && check body

theorem sound (program : Program) (hc : check program = true) : Shape program := by
  induction program with
  | code ops =>
    intro op hm
    exact op_sound op ((List.all_eq_true.mp hc) op hm)
  | append first second ihl ihr =>
    exact ⟨ihl (Bool.and_eq_true_iff.mp hc).1, ihr (Bool.and_eq_true_iff.mp hc).2⟩
  | «repeat» counter bound body ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have nums : counter < 21 ∧ bound.size ≤ 29 ∧ expressionCellLimit bound = 0 ∧ expressionInputLimit bound ≤ 3 :=
      of_decide_eq_true hh.1
    exact ⟨nums.1, nums.2.1, nums.2.2.1, nums.2.2.2, ih hh.2⟩

theorem fullBuild_shape : Shape fullBuild := sound fullBuild (by decide)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTShape
