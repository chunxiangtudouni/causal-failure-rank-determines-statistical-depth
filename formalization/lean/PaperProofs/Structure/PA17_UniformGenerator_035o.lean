module

public import PaperProofs.Structure.PA17_UniformGenerator_035j

/-! Shared syntax-directed local value contract for complete finite
templates. Runtime loop environments are quantified explicitly, including
zero, so it contains no execution trace or received output-code answer. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035o

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035j

def TemplateChecked (rom : PhysicalROM) (B heapWords : Nat) (environment : Nat → Nat) : Template → Prop
  | .empty => True
  | .word expression => ExprChecked rom environment B heapWords expression
  | .append left right => TemplateChecked rom B heapWords environment left ∧ TemplateChecked rom B heapWords environment right
  | .repeat counter bound body => ExprChecked rom environment B heapWords bound ∧
      ∀ value ≤ bound.eval rom environment, TemplateChecked rom B heapWords (Function.update environment counter value) body

theorem expression_checked_mono (expression : Expr) (rom : PhysicalROM) (heap : Nat → Nat) (B H largerB largerH : Nat)
    (hb : B ≤ largerB) (hh : H ≤ largerH) (hc : ExprChecked rom heap B H expression) :
    ExprChecked rom heap largerB largerH expression := by
  induction expression with
  | constant value => exact hc.trans hb
  | cell address => exact ⟨hc.1.trans_le hh, hc.2.1.trans hb, hc.2.2.trans hb⟩
  | input address => exact ⟨hc.1, hc.2.1.trans hb, hc.2.2.trans hb⟩
  | binary operation left right ihl ihr => exact ⟨ihl hc.1, ihr hc.2.1, hc.2.2.trans hb⟩

theorem template_checked_mono (template : Template) (rom : PhysicalROM) (environment : Nat → Nat) (B H largerB largerH : Nat)
    (hb : B ≤ largerB) (hh : H ≤ largerH) (hc : TemplateChecked rom B H environment template) :
    TemplateChecked rom largerB largerH environment template := by
  induction template generalizing environment with
  | empty => trivial
  | word expression => exact expression_checked_mono expression rom environment B H largerB largerH hb hh hc
  | append left right ihl ihr => exact ⟨ihl environment hc.1, ihr environment hc.2⟩
  | «repeat» counter bound body ih =>
    exact ⟨expression_checked_mono bound rom environment B H largerB largerH hb hh hc.1,
      fun value hv => ih _ (hc.2 value hv)⟩

theorem expression_checked_scoped (expression : Expr) (rom : PhysicalROM) (B heapWords : Nat)
    (scope : Finset Nat) (hs : expression.cells ⊆ scope) (environment heap : Nat → Nat)
    (he : EnvRep scope environment heap) (hc : ExprChecked rom environment B heapWords expression) :
    ExprChecked rom heap B heapWords expression := by
  induction expression with
  | constant value => exact hc
  | cell address =>
    refine ⟨hc.1, hc.2.1, ?_⟩
    rw [he address (hs (by simp [Expr.cells]))]
    exact hc.2.2
  | input address => exact hc
  | binary operation left right ihl ihr =>
    have hl : left.cells ⊆ scope := fun address hm => hs (Finset.mem_union_left _ hm)
    have hr : right.cells ⊆ scope := fun address hm => hs (Finset.mem_union_right _ hm)
    refine ⟨ihl hl hc.1, ihr hr hc.2.1, ?_⟩
    rw [Expr.eval_cells_congr left rom scope hl environment heap he, Expr.eval_cells_congr right rom scope hr environment heap he]
    exact hc.2.2

theorem template_checked_scoped (template : Template) (rom : PhysicalROM) (B heapWords : Nat)
    (scope : Finset Nat) (hs : template.WellScoped scope) (environment heap : Nat → Nat)
    (he : EnvRep scope environment heap) (hc : TemplateChecked rom B heapWords environment template) :
    TemplateChecked rom B heapWords heap template := by
  induction template generalizing scope environment heap with
  | empty => trivial
  | word expression => exact expression_checked_scoped expression rom B heapWords scope hs environment heap he hc
  | append left right ihl ihr => exact ⟨ihl scope hs.1 environment heap he hc.1, ihr scope hs.2 environment heap he hc.2⟩
  | «repeat» counter bound body ih =>
    refine ⟨expression_checked_scoped bound rom B heapWords scope hs.2.1 environment heap he hc.1, ?_⟩
    intro value hv
    rw [Expr.eval_cells_congr bound rom scope hs.2.1 environment heap he] at hv
    apply ih (insert counter scope) hs.2.2 (Function.update environment counter value) (Function.update heap counter value) ?_ (hc.2 value hv)
    intro address hm
    by_cases hz : address = counter
    · subst address; simp only [Function.update_self]
    · simp only [Function.update_of_ne hz]
      exact he address ((Finset.mem_insert.mp hm).resolve_left hz)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035o
