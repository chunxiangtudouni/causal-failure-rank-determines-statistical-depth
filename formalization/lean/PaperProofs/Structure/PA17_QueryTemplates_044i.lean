module
public import PaperProofs.Structure.PA17_QueryTemplates_044h
public import PaperProofs.Structure.PA17_UniformGenerator_035o

/-! A syntax-only certificate implies the actual recursive compiler value
contract, for every permitted lexical loop value including zero. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044i
open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
  PA17UniformGenerator035j PA17UniformGenerator035o PA17ProgramTemplates041 PA17QueryTemplates044h

deriving instance DecidableEq for Expr

def smallBounds : List Expr :=
  [.constant 0, .constant 1, .constant 2, .constant 3, .constant 4, .constant 5, .constant 6, .constant 7,
   .input 0, .input 1, .input 2, .binary .add (.input 1) (.constant 1),
   .binary .add (.input 1) (.constant 2), .binary .add (.input 2) (.constant 1)]

def SmallBound (bound : Expr) : Prop := bound ∈ smallBounds
def scale (N q size : Nat) : Nat := N + q + size + 8
def bound (N q size : Nat) : Nat := 1048576 * scale N q size ^ 3

theorem smallBound_le (expression : Expr) (hs : SmallBound expression) (N q size : Nat) (env : Nat → Nat) :
    expression.eval (dimensionROM N q size) env ≤ scale N q size := by
  simp only [SmallBound, smallBounds, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Expr.eval, Binary.eval, dimensionROM, PhysicalROM.semantic, PhysicalROM.words, scale]
  all_goals omega

def ExpressionProfile (scope : Finset Nat) (expression : Expr) : Prop :=
  Good expression ∧ expression.Below 64 ∧ expression.InputsBelow 3 ∧ expression.cells ⊆ scope ∧
    coefficient expression ≤ 1048576 ∧ degree expression ≤ 3

def Profile (scope : Finset Nat) : Template → Prop
  | .empty => True
  | .word expression => ExpressionProfile scope expression
  | .append left right => Profile scope left ∧ Profile scope right
  | .repeat counter count body => ExpressionProfile scope count ∧
      (counter ∈ scope → SmallBound count) ∧ Profile scope body

@[instance_reducible] def goodDec : (expression : Expr) → Decidable (Good expression)
  | .constant _ | .cell _ | .input _ => isTrue True.intro
  | .binary op left right => by
    letI := goodDec left
    letI := goodDec right
    change Decidable ((op = .add ∨ op = .subtract ∨ op = .minimum ∨ op = .multiply ∨ op = .divide) ∧ Good left ∧ Good right)
    infer_instance

@[instance_reducible] def expressionProfileDec (scope : Finset Nat) (expression : Expr) :
    Decidable (ExpressionProfile scope expression) := by
  letI := goodDec expression
  letI := PA17QueryTemplates044g.exprBelowDec 64 expression
  letI := PA17QueryTemplates044g.exprInputsDec 3 expression
  unfold ExpressionProfile
  infer_instance

@[instance_reducible] def profileDec (scope : Finset Nat) : (template : Template) → Decidable (Profile scope template)
  | .empty => isTrue True.intro
  | .word expression => expressionProfileDec scope expression
  | .append left right => by
    letI := profileDec scope left
    letI := profileDec scope right
    change Decidable (Profile scope left ∧ Profile scope right)
    infer_instance
  | .repeat counter count body => by
    letI := expressionProfileDec scope count
    letI := profileDec scope body
    change Decidable (ExpressionProfile scope count ∧ (counter ∈ scope → count ∈ smallBounds) ∧ Profile scope body)
    infer_instance

theorem profile_expression_checked (scope : Finset Nat) (expression : Expr)
    (hs : ExpressionProfile scope expression) (N q size heapWords : Nat) (hh : 64 ≤ heapWords)
    (env : Nat → Nat) (he : ∀ address ∈ scope, env address ≤ scale N q size) :
    ExprChecked (dimensionROM N q size) env (bound N q size) heapWords expression := by
  have hu : 1 ≤ scale N q size := by dsimp [scale]; omega
  have hpow : 1 ≤ scale N q size ^ 3 := by
    simpa using (pow_le_pow_right' hu (show 0 ≤ 3 by omega))
  have hB : 64 ≤ bound N q size := by dsimp [bound]; omega
  apply expression_checked expression _ env (scale N q size) (bound N q size) heapWords hu hB hh scope hs.2.2.2.1 he hs.2.1 hs.2.2.1
  · simp [dimensionROM]
  · intro address ha
    interval_cases address <;> simp [dimensionROM, PhysicalROM.semantic, PhysicalROM.words, scale] <;> omega
  · exact hs.1
  · exact budget_mono _ _ _ _ _ hu hs.2.2.2.2.1 hs.2.2.2.2.2

theorem profile_template_checked (scope : Finset Nat) (template : Template) (hs : Profile scope template)
    (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (env : Nat → Nat)
    (he : ∀ address ∈ scope, env address ≤ scale N q size) :
    TemplateChecked (dimensionROM N q size) (bound N q size) heapWords env template := by
  induction template generalizing env with
  | empty => trivial
  | word expression => exact profile_expression_checked scope expression hs N q size heapWords hh env he
  | append left right ihl ihr => exact ⟨ihl hs.1 env he, ihr hs.2 env he⟩
  | «repeat» counter count body ih =>
    refine ⟨profile_expression_checked scope count hs.1 N q size heapWords hh env he, ?_⟩
    intro value hv
    apply ih hs.2.2 (Function.update env counter value)
    intro address ha
    by_cases hac : address = counter
    · subst address
      rw [Function.update_self]
      exact hv.trans (smallBound_le count (hs.2.1 ha) N q size env)
    · rw [Function.update_of_ne hac]
      exact he address ha

def queryScope : Finset Nat := {17, 18, 19, 21}
attribute [local instance] profileDec

theorem query_profile : Profile queryScope PA17QueryTemplates044f.queryProgram.codeTemplate := by decide
theorem wrapped_profile : Profile queryScope PA17QueryTemplates044f.wrappedQuery.codeTemplate := by decide

theorem query_template_checked (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (env : Nat → Nat)
    (he : ∀ address ∈ queryScope, env address ≤ scale N q size) :
    TemplateChecked (dimensionROM N q size) (bound N q size) heapWords env PA17QueryTemplates044f.queryProgram.codeTemplate :=
  profile_template_checked queryScope _ query_profile N q size heapWords hh env he

theorem wrapped_template_checked (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (env : Nat → Nat)
    (he : ∀ address ∈ queryScope, env address ≤ scale N q size) :
    TemplateChecked (dimensionROM N q size) (bound N q size) heapWords env PA17QueryTemplates044f.wrappedQuery.codeTemplate :=
  profile_template_checked queryScope _ wrapped_profile N q size heapWords hh env he

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044i
