module

public import PaperProofs.Structure.PA17_UniformGenerator_035c

/-! Shared finite syntax for all six real dimension-only code templates.
Its compiler emits actual ordinary ISA code using the proved streaming
emitter and bounded-loop controller. Template denotation is only the proof
specification; it is never a ROM or generator input. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c

def Expr.cells : Expr → Finset Nat
  | .constant _ | .input _ => ∅
  | .cell address => {address}
  | .binary _ left right => left.cells ∪ right.cells

def Expr.InputsBelow (limit : Nat) : Expr → Prop
  | .constant _ | .cell _ => True
  | .input address => address < limit
  | .binary _ left right => left.InputsBelow limit ∧ right.InputsBelow limit

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035d

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c

inductive Template where
  | empty
  | word (expression : Expr)
  | append (left right : Template)
  | repeat (counter : Nat) (bound : Expr) (body : Template)

def Template.denote (rom : PhysicalROM) (environment : Nat → Nat) : Template → List Nat
  | .empty => []
  | .word expression => [expression.eval rom environment]
  | .append left right => left.denote rom environment ++ right.denote rom environment
  | .repeat counter bound body =>
      (List.range (bound.eval rom environment)).reverse.flatMap (fun index =>
        body.denote rom (Function.update environment counter (index + 1)))

def Template.sequence : List Template → Template
  | [] => .empty
  | first :: later => .append first (Template.sequence later)

def Template.words (expressions : List Expr) : Template :=
  Template.sequence (expressions.map Template.word)

def Template.literal (words : List Nat) : Template :=
  Template.words (words.map Expr.constant)

theorem Template.denote_sequence (rom : PhysicalROM) (environment : Nat → Nat) (templates : List Template) :
    (Template.sequence templates).denote rom environment = templates.flatMap (fun entry => entry.denote rom environment) := by
  induction templates with
  | nil => rfl
  | cons first later ih => simp only [Template.sequence, Template.denote, List.flatMap_cons, ih]

theorem Template.denote_words (rom : PhysicalROM) (environment : Nat → Nat) (expressions : List Expr) :
    (Template.words expressions).denote rom environment = expressions.map (fun expression => expression.eval rom environment) := by
  rw [Template.words, Template.denote_sequence]
  induction expressions with
  | nil => rfl
  | cons expression later ih => simp only [List.map_cons, List.flatMap_cons, Template.denote, List.singleton_append, ih]

theorem Template.denote_literal (rom : PhysicalROM) (environment : Nat → Nat) (words : List Nat) :
    (Template.literal words).denote rom environment = words := by
  rw [Template.literal, Template.denote_words, List.map_map]
  simp only [Expr.eval, Function.comp_def]
  exact List.map_id words

/-- Active loop scope are lexical. A child loop uses a fresh counter;
it may reuse that cell in another sequential child after it has exited. -/
def Template.WellScoped (scope : Finset Nat) : Template → Prop
  | .empty => True
  | .word expression => expression.cells ⊆ scope
  | .append left right => left.WellScoped scope ∧ right.WellScoped scope
  | .repeat counter bound body => counter ∉ scope ∧ bound.cells ⊆ scope ∧ body.WellScoped (insert counter scope)

def Template.Below (stack : Nat) : Template → Prop
  | .empty => True
  | .word expression => expression.Below stack
  | .append left right => left.Below stack ∧ right.Below stack
  | .repeat counter bound body => counter < stack ∧ bound.Below stack ∧ body.Below stack

def Template.StackFits (stack outputBase : Nat) : Template → Prop
  | .empty => True
  | .word expression => stack + expression.size ≤ outputBase
  | .append left right => left.StackFits stack outputBase ∧ right.StackFits stack outputBase
  | .repeat _ bound body => stack + bound.size ≤ outputBase ∧ body.StackFits stack outputBase

def Template.InputsBelow (limit : Nat) : Template → Prop
  | .empty => True
  | .word expression => expression.InputsBelow limit
  | .append left right => left.InputsBelow limit ∧ right.InputsBelow limit
  | .repeat _ bound body => bound.InputsBelow limit ∧ body.InputsBelow limit

def bind (expression : Expr) (stack target : Nat) : List PackingOp :=
  expression.compile stack ++ spill target

def Template.codeLength (stack : Nat) : Template → Nat
  | .empty => 0
  | .word expression => (expression.compile stack).length + 8
  | .append left right => left.codeLength stack + right.codeLength stack
  | .repeat _ bound body => (bound.compile stack).length + 2 + body.codeLength stack + 12

def Template.compile (stack cursor outputBase start : Nat) : Template → List PackingOp
  | .empty => []
  | .word expression => emitWord expression stack cursor outputBase
  | .append left right => left.compile stack cursor outputBase start ++
      right.compile stack cursor outputBase (start + left.codeLength stack)
  | .repeat counter bound body =>
      let pre := bind bound stack counter
      pre ++ loopBlock counter (start + pre.length)
        (body.compile stack cursor outputBase (start + pre.length + 4))

theorem Template.compile_length (template : Template) (stack cursor outputBase start : Nat) :
    (template.compile stack cursor outputBase start).length = template.codeLength stack := by
  induction template generalizing start with
  | empty => rfl
  | word expression => exact emitWord_length expression stack cursor outputBase
  | append left right ihl ihr =>
    simp only [Template.compile, Template.codeLength, List.length_append, ihl, ihr]
  | «repeat» counter bound body ih =>
    simp only [Template.compile, Template.codeLength, List.length_append, loopBlock_length, ih,
      bind, spill, List.length_cons, List.length_nil]
    omega

theorem Template.compile_length_independent_start (template : Template) (stack cursor outputBase left right : Nat) :
    (template.compile stack cursor outputBase left).length = (template.compile stack cursor outputBase right).length := by
  rw [template.compile_length, template.compile_length]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035d

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c

theorem Expr.eval_cells_congr (expression : Expr) (rom : PhysicalROM) (scope : Finset Nat)
    (hs : expression.cells ⊆ scope) (environment environment' : Nat → Nat)
    (he : ∀ address ∈ scope, environment' address = environment address) :
    expression.eval rom environment' = expression.eval rom environment := by
  induction expression with
  | constant value => rfl
  | cell address => exact he address (hs (by simp [Expr.cells]))
  | input address => rfl
  | binary operation left right ihl ihr =>
    have hl : left.cells ⊆ scope := fun address hm => hs (Finset.mem_union_left _ hm)
    have hr : right.cells ⊆ scope := fun address hm => hs (Finset.mem_union_right _ hm)
    simp only [Expr.eval, ihl hl, ihr hr]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035d

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c

theorem Template.denote_scoped (template : Template) (rom : PhysicalROM) (scope : Finset Nat)
    (hs : template.WellScoped scope) (environment environment' : Nat → Nat)
    (he : ∀ address ∈ scope, environment' address = environment address) :
    template.denote rom environment' = template.denote rom environment := by
  induction template generalizing scope environment environment' with
  | empty => rfl
  | word expression =>
    simp only [Template.denote]
    rw [Expr.eval_cells_congr expression rom scope hs environment environment' he]
  | append left right ihl ihr =>
    simp only [Template.denote]
    rw [ihl scope hs.1 environment environment' he, ihr scope hs.2 environment environment' he]
  | «repeat» counter bound body ih =>
    simp only [Template.denote]
    rw [Expr.eval_cells_congr bound rom scope hs.2.1 environment environment' he]
    apply List.flatMap_congr
    intro index _
    apply ih (insert counter scope) hs.2.2
    intro address ha
    by_cases hz : address = counter
    · subst address
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hz]
      exact he address ((Finset.mem_insert.mp ha).resolve_left hz)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035d
