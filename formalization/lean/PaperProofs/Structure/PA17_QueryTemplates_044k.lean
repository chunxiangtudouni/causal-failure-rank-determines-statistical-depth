module
public import PaperProofs.Structure.PA17_QueryTemplates_044i

/-! A parameterized syntax contract for other actual full/rolling ASTs.
The scope, environment ceiling and allowed tracked-loop bounds are parameters. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044k
open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
  PA17UniformGenerator035j PA17UniformGenerator035o PA17QueryTemplates044h PA17QueryTemplates044i

def ProfileWith (scope : Finset Nat) (smallBound : Expr → Prop) : Template → Prop
  | .empty => True
  | .word expression => ExpressionProfile scope expression
  | .append left right => ProfileWith scope smallBound left ∧ ProfileWith scope smallBound right
  | .repeat counter count body => ExpressionProfile scope count ∧
      (counter ∈ scope → smallBound count) ∧ ProfileWith scope smallBound body

@[instance_reducible] def profileWithDec (scope : Finset Nat) (smallBound : Expr → Prop)
    [DecidablePred smallBound] : (template : Template) → Decidable (ProfileWith scope smallBound template)
  | .empty => isTrue True.intro
  | .word expression => expressionProfileDec scope expression
  | .append left right => by
    letI := profileWithDec scope smallBound left
    letI := profileWithDec scope smallBound right
    change Decidable (ProfileWith scope smallBound left ∧ ProfileWith scope smallBound right)
    infer_instance
  | .repeat counter count body => by
    letI := expressionProfileDec scope count
    letI := profileWithDec scope smallBound body
    change Decidable (ExpressionProfile scope count ∧ (counter ∈ scope → smallBound count) ∧ ProfileWith scope smallBound body)
    infer_instance

theorem profile_expression_generic (scope : Finset Nat) (expression : Expr)
    (hs : ExpressionProfile scope expression) (rom : PhysicalROM) (u B heapWords : Nat)
    (hu : 1 ≤ u) (hB : 64 ≤ B) (hh : 64 ≤ heapWords) (hbudget : 1048576 * u ^ 3 ≤ B)
    (hi : 3 ≤ rom.input.length) (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u)
    (env : Nat → Nat) (he : ∀ address ∈ scope, env address ≤ u) : ExprChecked rom env B heapWords expression := by
  apply expression_checked expression rom env u B heapWords hu hB hh scope hs.2.2.2.1 he hs.2.1 hs.2.2.1 hi hinput hs.1
  exact (budget_mono _ _ _ _ _ hu hs.2.2.2.2.1 hs.2.2.2.2.2).trans hbudget

theorem profileWith_template_checked (scope : Finset Nat) (smallBound : Expr → Prop)
    (template : Template) (hs : ProfileWith scope smallBound template) (rom : PhysicalROM)
    (u B heapWords : Nat) (hu : 1 ≤ u) (hB : 64 ≤ B) (hh : 64 ≤ heapWords)
    (hbudget : 1048576 * u ^ 3 ≤ B) (hi : 3 ≤ rom.input.length)
    (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u)
    (hsmall : ∀ expression, smallBound expression → ∀ environment : Nat → Nat,
      (∀ address ∈ scope, environment address ≤ u) → expression.eval rom environment ≤ u)
    (env : Nat → Nat) (he : ∀ address ∈ scope, env address ≤ u) :
    TemplateChecked rom B heapWords env template := by
  induction template generalizing env with
  | empty => trivial
  | word expression => exact profile_expression_generic scope expression hs rom u B heapWords hu hB hh hbudget hi hinput env he
  | append left right ihl ihr => exact ⟨ihl hs.1 env he, ihr hs.2 env he⟩
  | «repeat» counter count body ih =>
    refine ⟨profile_expression_generic scope count hs.1 rom u B heapWords hu hB hh hbudget hi hinput env he, ?_⟩
    intro value hv
    apply ih hs.2.2 (Function.update env counter value)
    intro address ha
    by_cases hac : address = counter
    · subst address
      rw [Function.update_self]
      exact hv.trans (hsmall count (hs.2.1 ha) env he)
    · rw [Function.update_of_ne hac]
      exact he address ha

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044k
