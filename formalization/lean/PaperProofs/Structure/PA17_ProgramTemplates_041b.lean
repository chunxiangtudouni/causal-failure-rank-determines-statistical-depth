module
public import PaperProofs.Structure.PA17_ProgramTemplates_041a
public import PaperProofs.Structure.PA17_UniformGenerator_035d

/-! Finite structured templates retain the original opcode structure.
Their lowering emits the exact existing five-word encoding and terminal
HALT, using only expression compilation and actual bounded generator loops. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d

inductive Program where
  | code (ops : List OpExpr)
  | append (left right : Program)
  | repeat (counter : Nat) (bound : Expr) (body : Program)

def Program.eval (rom : PhysicalROM) (environment : Nat → Nat) : Program → List Op
  | .code ops => instructions rom environment ops
  | .append left right => left.eval rom environment ++ right.eval rom environment
  | .repeat counter bound body => (List.range (bound.eval rom environment)).reverse.flatMap
      (fun index => body.eval rom (Function.update environment counter (index + 1)))

def Program.toTemplate : Program → Template
  | .code ops => Template.words (expressions ops)
  | .append left right => .append left.toTemplate right.toTemplate
  | .repeat counter bound body => .repeat counter bound body.toTemplate

theorem Program.toTemplate_denote (program : Program) (rom : PhysicalROM) (environment : Nat → Nat) :
    program.toTemplate.denote rom environment = IndexedClosureRAM.programWords (program.eval rom environment) := by
  induction program generalizing environment with
  | code ops =>
    rw [Program.toTemplate, Template.denote_words]
    exact expressions_eval ops rom environment
  | append left right ihl ihr =>
    simp only [Program.toTemplate, Template.denote, Program.eval, ihl, ihr,
      IndexedClosureRAM.programWords, List.flatMap_append]
  | «repeat» counter bound body ih =>
    simp only [Program.toTemplate, Template.denote, Program.eval,
      IndexedClosureRAM.programWords, List.flatMap_assoc]
    apply List.flatMap_congr
    intro index _
    exact ih (Function.update environment counter (index + 1))

def Program.haltingTemplate (program : Program) : Template :=
  .append program.toTemplate (Template.literal haltWords.toArray.toList)

theorem Program.haltingTemplate_denote (program : Program) (rom : PhysicalROM) (environment : Nat → Nat) :
    program.haltingTemplate.denote rom environment = haltingWords (program.eval rom environment) := by
  simp only [Program.haltingTemplate, Template.denote, Template.denote_literal,
    Program.toTemplate_denote, haltingWords]

def Program.sequence : List Program → Program
  | [] => .code []
  | first :: later => .append first (Program.sequence later)

theorem Program.sequence_eval (rom : PhysicalROM) (environment : Nat → Nat) (programs : List Program) :
    (Program.sequence programs).eval rom environment = programs.flatMap (fun program => program.eval rom environment) := by
  induction programs with
  | nil => rfl
  | cons first later ih => simp only [Program.sequence, Program.eval, List.flatMap_cons, ih]

def OpExpr.add (target left right : Register) : OpExpr := .literal (.base (.add target left right))
def OpExpr.minimum (target left right : Register) : OpExpr := .literal (.base (.minimum target left right))
def OpExpr.select (target condition whenTrue whenFalse : Register) : OpExpr :=
  .literal (.base (.select target condition whenTrue whenFalse))
def OpExpr.loadROM (region : Region) (target pointer : Register) : OpExpr := .literal (.base (.loadROM region target pointer))
def OpExpr.loadHeap (target pointer : Register) : OpExpr := .literal (.base (.loadHeap target pointer))
def OpExpr.storeHeap (pointer source : Register) : OpExpr := .literal (.base (.storeHeap pointer source))
def OpExpr.subtract (target left right : Register) : OpExpr := .literal (.subtract target left right)

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
