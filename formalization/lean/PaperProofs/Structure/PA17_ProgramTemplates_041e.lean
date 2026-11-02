module
public import PaperProofs.Structure.PA17_ProgramTemplates_041d

/-! Runtime length prefixes are computed from the finite source template.
No complete generated program is received as a ROM, list or oracle. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d

def Program.lengthExpr : Program → Expr
  | .code ops => .constant ops.length
  | .append left right => .binary .add left.lengthExpr right.lengthExpr
  | .repeat _ bound body => .binary .multiply bound body.lengthExpr

def Program.UniformLength : Program → Prop
  | .code _ => True
  | .append left right => left.UniformLength ∧ right.UniformLength
  | .repeat counter _ body => counter ∉ body.lengthExpr.cells ∧ body.UniformLength

theorem Program.length_eval (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hs : program.UniformLength) : (program.eval rom environment).length = program.lengthExpr.eval rom environment := by
  induction program generalizing environment with
  | code ops => simp only [Program.eval, instructions, List.length_map, Program.lengthExpr, Expr.eval]
  | append left right ihl ihr =>
    simp only [Program.eval, List.length_append, Program.lengthExpr, Expr.eval, Binary.eval]
    rw [ihl environment hs.1, ihr environment hs.2]
  | «repeat» counter bound body ih =>
    have hbody (index : Nat) :
        (body.eval rom (Function.update environment counter (index + 1))).length = body.lengthExpr.eval rom environment :=
      (ih _ hs.2).trans (eval_update_of_not_mem body.lengthExpr rom environment counter (index + 1) hs.1)
    simp only [Program.eval, List.length_flatMap, hbody, Program.lengthExpr, Expr.eval, Binary.eval,
      List.map_const', List.length_reverse, List.length_range, List.sum_replicate, Nat.nsmul_eq_mul]

def Program.haltingLengthExpr (program : Program) : Expr :=
  .binary .add (.binary .multiply (.constant 5) program.lengthExpr) (.constant 5)

theorem Program.haltingLengthExpr_eval (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hs : program.UniformLength) :
    program.haltingLengthExpr.eval rom environment = (haltingWords (program.eval rom environment)).length := by
  rw [Program.haltingLengthExpr, Expr.eval, Expr.eval, Expr.eval, Expr.eval, Binary.eval, Binary.eval,
    ← Program.length_eval program rom environment hs, haltingWords_length]

def Program.codeTemplate (program : Program) : Template :=
  .append (.word program.haltingLengthExpr) program.haltingTemplate

theorem Program.codeTemplate_denote (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hs : program.UniformLength) :
    program.codeTemplate.denote rom environment =
      (haltingWords (program.eval rom environment)).length :: haltingWords (program.eval rom environment) := by
  simp only [Program.codeTemplate, Template.denote, Program.haltingTemplate_denote,
    Program.haltingLengthExpr_eval program rom environment hs, List.singleton_append]

theorem metadataProgram_uniformLength (base : Expr) : (metadataProgram base).UniformLength := by
  dsimp [Program.UniformLength, metadataProgram, metadataClear, metadataNode, Program.sequence,
    Program.lengthExpr, metadataBit, metadataTail, Expr.cells, qDim, tDim]
  decide

theorem fullMetadata_codeTemplate (N q size : Nat) (environment : Nat → Nat) :
    (metadataProgram fullCapacity).codeTemplate.denote (dimensionROM N q size) environment =
      (haltingWords (UniformTreeMetadataRAM.program N q size (PA17CellLayout003.capacityWords N q size))).length ::
        haltingWords (UniformTreeMetadataRAM.program N q size (PA17CellLayout003.capacityWords N q size)) := by
  rw [Program.codeTemplate_denote _ _ _ (metadataProgram_uniformLength _),
    metadataProgram_eval fullCapacity fullCapacity_cells, fullCapacity_eval]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
