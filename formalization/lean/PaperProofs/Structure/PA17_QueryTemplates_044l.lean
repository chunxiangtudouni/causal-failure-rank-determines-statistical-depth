module
public import PaperProofs.Structure.PA17_QueryTemplates_044i
public import PaperProofs.Structure.PA17_UniformGenerator_035n

/-! Syntax-derived productive-loop certificates for the whole real query.
Loop overhead is charged to emitted words by the original compiler clock. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044l
open AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035e
  PA17UniformGenerator035n PA17ProgramTemplates041

def lowerWords (positiveBound : Expr → Bool) : Template → Nat
  | .empty => 0
  | .word _ => 1
  | .append left right => lowerWords positiveBound left + lowerWords positiveBound right
  | .repeat _ count body => if positiveBound count = true then lowerWords positiveBound body else 0

def ProductiveShape (positiveBound : Expr → Bool) : Template → Prop
  | .empty | .word _ => True
  | .append left right => ProductiveShape positiveBound left ∧ ProductiveShape positiveBound right
  | .repeat _ _ body => 0 < lowerWords positiveBound body ∧ ProductiveShape positiveBound body

theorem lowerWords_le (positiveBound : Expr → Bool) (template : Template) (rom : PhysicalROM)
    (hpositive : ∀ expression, positiveBound expression = true → ∀ env : Nat → Nat, 0 < expression.eval rom env)
    (env : Nat → Nat) : lowerWords positiveBound template ≤ (template.denote rom env).length := by
  induction template generalizing env with
  | empty => exact le_rfl
  | word expression => exact le_rfl
  | append left right ihl ihr =>
    simpa only [lowerWords, Template.denote, List.length_append] using Nat.add_le_add (ihl env) (ihr env)
  | «repeat» counter count body ih =>
    by_cases hp : positiveBound count = true
    · simp only [lowerWords, hp, ite_true]
      have hn := hpositive count hp env
      obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
      change lowerWords positiveBound body ≤ (loopWords rom env counter body (count.eval rom env)).length
      rw [hfuel, loopWords_succ, List.length_append]
      exact (ih _).trans (Nat.le_add_right _ _)
    · rw [lowerWords, ite_eq_right hp]
      exact Nat.zero_le _

theorem shape_productive (positiveBound : Expr → Bool) (template : Template)
    (hs : ProductiveShape positiveBound template) (rom : PhysicalROM)
    (hpositive : ∀ expression, positiveBound expression = true → ∀ env : Nat → Nat, 0 < expression.eval rom env)
    (env : Nat → Nat) : Productive rom env template := by
  induction template generalizing env with
  | empty => trivial
  | word expression => trivial
  | append left right ihl ihr => exact ⟨ihl hs.1 env, ihr hs.2 env⟩
  | «repeat» counter count body ih =>
    intro index _
    exact ⟨hs.1.trans_le (lowerWords_le positiveBound body rom hpositive _), ih hs.2 _⟩

@[instance_reducible] def shapeDec (positiveBound : Expr → Bool) :
    (template : Template) → Decidable (ProductiveShape positiveBound template)
  | .empty | .word _ => isTrue True.intro
  | .append left right => by
    letI := shapeDec positiveBound left
    letI := shapeDec positiveBound right
    change Decidable (ProductiveShape positiveBound left ∧ ProductiveShape positiveBound right)
    infer_instance
  | .repeat _ _ body => by
    letI := shapeDec positiveBound body
    change Decidable (0 < lowerWords positiveBound body ∧ ProductiveShape positiveBound body)
    infer_instance

def queryPositive (expression : Expr) : Bool := decide (expression = .input 2)

attribute [local instance] shapeDec
theorem query_shape : ProductiveShape queryPositive PA17QueryTemplates044f.queryProgram.codeTemplate := by decide
theorem wrapped_shape : ProductiveShape queryPositive PA17QueryTemplates044f.wrappedQuery.codeTemplate := by decide

theorem queryPositive_eval (N q size : Nat) (ht : 0 < size) :
    ∀ expression, queryPositive expression = true → ∀ env : Nat → Nat, 0 < expression.eval (dimensionROM N q size) env := by
  intro expression he env
  have heq : expression = .input 2 := of_decide_eq_true he
  subst expression
  exact ht

theorem query_productive (N q size : Nat) (ht : 0 < size) (env : Nat → Nat) :
    Productive (dimensionROM N q size) env PA17QueryTemplates044f.queryProgram.codeTemplate :=
  shape_productive queryPositive _ query_shape _ (queryPositive_eval N q size ht) env

theorem wrapped_productive (N q size : Nat) (ht : 0 < size) (env : Nat → Nat) :
    Productive (dimensionROM N q size) env PA17QueryTemplates044f.wrappedQuery.codeTemplate :=
  shape_productive queryPositive _ wrapped_shape _ (queryPositive_eval N q size ht) env

theorem wrapped_clock_le_output (N q size : Nat) (ht : 0 < size) (env : Nat → Nat) :
    clock (dimensionROM N q size) env 64 PA17QueryTemplates044f.wrappedQuery.codeTemplate ≤
      factor 64 PA17QueryTemplates044f.wrappedQuery.codeTemplate *
        ((PA17QueryTemplates044f.wrappedQuery.codeTemplate.denote (dimensionROM N q size) env).length + 1) :=
  clock_le_output _ _ _ 64 (wrapped_productive N q size ht env)

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044l
