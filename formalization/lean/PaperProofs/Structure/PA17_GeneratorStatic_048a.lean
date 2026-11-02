module
public import PaperProofs.Structure.PA17_UniformGenerator_035ac
public import PaperProofs.Structure.PA17_UniformGenerator_035n

/-! Fixed-syntax bounds avoid expanding the complete generated instruction
list merely to count it. Every expression is charged by its actual AST size. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048

open PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035n

def codeBound : Template → Nat
  | .empty => 0
  | .word expression => 5 * expression.size + 8
  | .append left right => codeBound left + codeBound right
  | .repeat _ bound body => 5 * bound.size + 2 + codeBound body + 12

def factorBound : Template → Nat
  | .empty => 1
  | .word expression => 5 * expression.size + 8
  | .append left right => factorBound left + factorBound right
  | .repeat _ bound body => 5 * bound.size + 2 * factorBound body + 18

theorem codeLength_le_bound (template : Template) (stack : Nat) :
    template.codeLength stack ≤ codeBound template := by
  induction template with
  | empty => exact le_rfl
  | word expression =>
    exact Nat.add_le_add_right (Expr.compile_length_le expression stack) 8
  | append left right ihl ihr => exact Nat.add_le_add ihl ihr
  | «repeat» counter bound body ih =>
    have he := Expr.compile_length_le bound stack
    dsimp only [Template.codeLength, codeBound]
    omega

theorem factor_le_bound (template : Template) (stack : Nat) :
    factor stack template ≤ factorBound template := by
  induction template with
  | empty => exact le_rfl
  | word expression =>
    exact Nat.add_le_add_right (Expr.compile_length_le expression stack) 8
  | append left right ihl ihr => exact Nat.add_le_add ihl ihr
  | «repeat» counter bound body ih =>
    have he := Expr.compile_length_le bound stack
    dsimp only [factor, factorBound]
    omega

def codeSumBound (templates : List Template) : Nat :=
  (templates.map (fun template => codeBound template + 23)).sum

def factorSumBound (templates : List Template) : Nat :=
  (templates.map (fun template => factorBound template + 23)).sum

theorem streamLength_le_bound (templates : List Template) (stack : Nat) :
    PA17UniformGenerator035ac.streamLength stack templates ≤ codeSumBound templates := by
  induction templates with
  | nil => exact le_rfl
  | cons first later ih =>
    have he := codeLength_le_bound first stack
    simp only [PA17UniformGenerator035ac.streamLength, codeSumBound, List.map_cons, List.sum_cons] at *
    omega

theorem factorSum_le_bound (templates : List Template) (stack : Nat) :
    (templates.map (fun template => factor stack template + 23)).sum ≤ factorSumBound templates := by
  induction templates with
  | nil => exact le_rfl
  | cons first later ih =>
    have he := factor_le_bound first stack
    simp only [factorSumBound, List.map_cons, List.sum_cons] at *
    omega

end PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048
