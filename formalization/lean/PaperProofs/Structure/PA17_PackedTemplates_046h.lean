module
public import PaperProofs.Structure.PA17_PackedTemplates_046g
public import PaperProofs.Structure.PA17_QueryTemplates_044h
public import PaperProofs.Structure.PA17_UniformGenerator_035o

/-! A finite syntactic certificate for actual physical-template expressions.
Masks use their proved safe shift construction; all other subexpressions
use polynomial envelopes of degree at most four. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
  PA17UniformGenerator035j PA17UniformGenerator035o PA17QueryTemplates044h

def ExpressionProfile (scope : Finset Nat) (expression : Expr) : Prop :=
  (expression = safeMask (.cell 1) ∨ expression = safeMask (.cell 2)) ∨
    (Good expression ∧ expression.Below 64 ∧ expression.InputsBelow 3 ∧ expression.cells ⊆ scope ∧
      coefficient expression ≤ 4096 ∧ degree expression ≤ 4)

def Profile (scope : Finset Nat) (smallBound : Expr → Prop) : Template → Prop
  | .empty => True
  | .word expression => ExpressionProfile scope expression
  | .append left right => Profile scope smallBound left ∧ Profile scope smallBound right
  | .repeat counter count body => ExpressionProfile scope count ∧ counter ≠ 1 ∧ counter ≠ 2 ∧
      (counter ∈ scope → smallBound count) ∧ Profile scope smallBound body

def MaskEnvironment (bits : Nat) (environment : Nat → Nat) : Prop :=
  0 < environment 1 ∧ environment 1 ≤ bits ∧ environment 2 = bits

theorem profile_expression_checked (scope : Finset Nat) (expression : Expr)
    (hs : ExpressionProfile scope expression) (rom : PhysicalROM) (u bits B heapWords : Nat)
    (h1 : 1 ∈ scope) (h2 : 2 ∈ scope) (hu : 1 ≤ u) (hB : 64 ≤ B) (hh : 64 ≤ heapWords)
    (hbudget : 4096 * u ^ 4 ≤ B) (hmax : 2 ^ bits - 1 ≤ B) (hbits : 0 < bits)
    (hi : 3 ≤ rom.input.length) (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u)
    (environment : Nat → Nat) (he : ∀ address ∈ scope, environment address ≤ u)
    (hm : MaskEnvironment bits environment) : ExprChecked rom environment B heapWords expression := by
  have huB : u ≤ B := by
    have hp : u ≤ u ^ 4 := by simpa using (pow_le_pow_right' hu (show 1 ≤ 4 by decide))
    omega
  have hcell (address : Nat) (ha : address ∈ scope) (hlt : address < 64) :
      ExprChecked rom environment B heapWords (.cell address) :=
    ⟨by omega, by omega, (he address ha).trans huB⟩
  rcases hs with (rfl | rfl) | hs
  · exact safeMask_checked (.cell 1) rom environment bits B heapWords
      (hcell 1 h1 (by decide)) hm.1 hm.2.1 (by omega) hmax
  · apply safeMask_checked (.cell 2) rom environment bits B heapWords
      (hcell 2 h2 (by decide))
    · simpa only [Expr.eval, hm.2.2] using hbits
    · change environment 2 ≤ bits
      exact le_of_eq hm.2.2
    · omega
    · exact hmax
  · apply expression_checked expression rom environment u B heapWords hu hB hh scope
      hs.2.2.2.1 he hs.2.1 hs.2.2.1 hi hinput hs.1
    exact (budget_mono _ _ _ _ _ hu hs.2.2.2.2.1 hs.2.2.2.2.2).trans hbudget

theorem profile_template_checked (scope : Finset Nat) (smallBound : Expr → Prop)
    (template : Template) (hp : Profile scope smallBound template) (rom : PhysicalROM)
    (u bits B heapWords : Nat) (h1 : 1 ∈ scope) (h2 : 2 ∈ scope)
    (hu : 1 ≤ u) (hB : 64 ≤ B) (hh : 64 ≤ heapWords)
    (hbudget : 4096 * u ^ 4 ≤ B) (hmax : 2 ^ bits - 1 ≤ B) (hbits : 0 < bits)
    (hi : 3 ≤ rom.input.length) (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u)
    (hsmall : ∀ expression, smallBound expression → ∀ environment : Nat → Nat,
      (∀ address ∈ scope, environment address ≤ u) → expression.eval rom environment ≤ u)
    (environment : Nat → Nat) (he : ∀ address ∈ scope, environment address ≤ u)
    (hm : MaskEnvironment bits environment) : TemplateChecked rom B heapWords environment template := by
  induction template generalizing environment with
  | empty => trivial
  | word expression =>
    exact profile_expression_checked scope expression hp rom u bits B heapWords
      h1 h2 hu hB hh hbudget hmax hbits hi hinput environment he hm
  | append left right ihl ihr => exact ⟨ihl hp.1 environment he hm, ihr hp.2 environment he hm⟩
  | «repeat» counter count body ih =>
    refine ⟨profile_expression_checked scope count hp.1 rom u bits B heapWords
      h1 h2 hu hB hh hbudget hmax hbits hi hinput environment he hm, ?_⟩
    intro value hv
    apply ih hp.2.2.2.2 (Function.update environment counter value)
    · intro address ha
      by_cases hac : address = counter
      · subst address
        rw [Function.update_self]
        exact hv.trans (hsmall count (hp.2.2.2.1 ha) environment he)
      · rw [Function.update_of_ne hac]
        exact he address ha
    · simpa only [MaskEnvironment, Function.update_of_ne hp.2.1.symm,
        Function.update_of_ne hp.2.2.1.symm] using hm

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
