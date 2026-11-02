module

public import Structure.PSTR_BuildLower_ASTExprBounds_035

/-! Source-list shape used in actual structured-loop induction. Every loop
bound in the fixed AST has no lexical cells, so body list lengths are stable
across countdown environments. Nonempty loop bodies are checked on the
original fixed syntax; this file asserts no machine runtime bound. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ProgramShape
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041

theorem zero_cells_eval (expr : Expr) (h : expressionCellLimit expr = 0) (rom : PhysicalROM) (left right : Nat → Nat) :
    expr.eval rom left = expr.eval rom right := by
  induction expr with
  | constant value => rfl
  | cell address => simp only [expressionCellLimit] at h; omega
  | input address => rfl
  | binary operation first second ihl ihr =>
    have hl : expressionCellLimit first = 0 := by change max _ _ = 0 at h; omega
    have hr : expressionCellLimit second = 0 := by change max _ _ = 0 at h; omega
    change operation.eval (first.eval rom left) (second.eval rom left) = operation.eval (first.eval rom right) (second.eval rom right)
    rw [ihl hl, ihr hr]

theorem eval_length_congr (program : Program) (rom : PhysicalROM) (left right : Nat → Nat)
    (hc : ExprBounds.programLoopsCertified program = true) :
    (program.eval rom left).length = (program.eval rom right).length := by
  induction program generalizing left right with
  | code ops => simp only [Program.eval, instructions, List.length_map]
  | append first second ihl ihr =>
    have hh := Bool.and_eq_true_iff.mp hc
    simp only [Program.eval, List.length_append, ihl left right hh.1, ihr left right hh.2]
  | «repeat» counter bound body ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have hb := Bool.and_eq_true_iff.mp hh.1
    have nums : expressionCellLimit bound = 0 ∧ ExprBounds.coefficient bound ≤ 4 ∧ ExprBounds.degree bound ≤ 1 :=
      of_decide_eq_true hb.2
    have he := zero_cells_eval bound nums.1 rom left right
    simp only [Program.eval, List.length_flatMap, he]
    apply congrArg List.sum
    apply List.map_congr_left
    intro index _
    exact ih (Function.update left counter (index + 1)) (Function.update right counter (index + 1)) hh.2

def positiveBound : Expr → Bool
  | .constant value => decide (0 < value)
  | .binary .add first second => positiveBound first || positiveBound second
  | .binary .multiply first second => positiveBound first && positiveBound second
  | _ => false

theorem positiveBound_sound (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (hc : positiveBound expr = true) : 0 < expr.eval rom environment := by
  induction expr with
  | constant value => exact of_decide_eq_true hc
  | cell address => simp only [positiveBound, Bool.false_eq_true] at hc
  | input address => simp only [positiveBound, Bool.false_eq_true] at hc
  | binary operation first second ihl ihr =>
    cases operation with
    | add =>
      rcases Bool.or_eq_true_iff.mp hc with hl | hr
      · have hh := ihl hl
        change 0 < first.eval rom environment + second.eval rom environment
        omega
      · have hh := ihr hr
        change 0 < first.eval rom environment + second.eval rom environment
        omega
    | multiply =>
      have hh := Bool.and_eq_true_iff.mp hc
      exact Nat.mul_pos (ihl hh.1) (ihr hh.2)
    | subtract | minimum | divide | bitAnd | bitOr | shiftLeft | shiftRight =>
      simp only [positiveBound, Bool.false_eq_true] at hc

def hasStep : Program → Bool
  | .code ops => !ops.isEmpty
  | .append first second => hasStep first || hasStep second
  | .repeat _ bound body => positiveBound bound && hasStep body

theorem hasStep_positive (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hc : hasStep program = true) : 0 < (program.eval rom environment).length := by
  induction program generalizing environment with
  | code ops =>
    cases ops with
    | nil => simp [hasStep] at hc
    | cons op later => simp only [Program.eval, instructions, List.length_map, List.length_cons]; omega
  | append first second ihl ihr =>
    rcases Bool.or_eq_true_iff.mp hc with h | h
    · have hh := ihl environment h
      simp only [Program.eval, List.length_append]
      omega
    · have hh := ihr environment h
      simp only [Program.eval, List.length_append]
      omega
  | «repeat» counter bound body ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have hb := positiveBound_sound bound rom environment hh.1
    have he : bound.eval rom environment = (bound.eval rom environment - 1) + 1 := by omega
    have hbody := ih (Function.update environment counter ((bound.eval rom environment - 1) + 1)) hh.2
    change 0 < ((List.range (bound.eval rom environment)).reverse.flatMap
      (fun index => body.eval rom (Function.update environment counter (index + 1)))).length
    rw [he, List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.flatMap_cons, List.length_append]
    omega

def nonemptyBodies : Program → Bool
  | .code _ => true
  | .append first second => nonemptyBodies first && nonemptyBodies second
  | .repeat _ _ body => hasStep body && nonemptyBodies body

theorem fullBuild_nonemptyBodies : nonemptyBodies fullBuild = true := by decide

theorem fullBuild_length_congr (N q t : Nat) (left right : Nat → Nat) :
    (fullBuild.eval (dimensionROM N q t) left).length = (fullBuild.eval (dimensionROM N q t) right).length :=
  eval_length_congr fullBuild _ left right ExprBounds.fullBuild_loops_certified

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ProgramShape
