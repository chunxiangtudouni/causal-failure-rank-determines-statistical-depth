module
public import PaperProofs.Structure.PA17_QueryTemplates_044e
public import PaperProofs.Structure.PA17_ProgramTemplates_041h
public import PaperProofs.Structure.PA17_WrappedNatRAM_038a

/-! Dimension-only fixed ASTs for the original whole Query019 body and
its exact logical spill wrapper in the final implementation038. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044f
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041
local instance pa17OfNat044f (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add044f : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Mul044f : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def metadata : Expr := fullCapacity
def parents : Expr := metadata + tDim
def labels : Expr := metadata + 3 * tDim + 1 + nDim
def counts : Expr := labels + tDim
def header : Expr := counts + tDim
def goodFlags : Expr := header + 16
def badFlags : Expr := goodFlags + qDim + 2
def children : Expr := badFlags + qDim + 2
def tool : Expr := children + tDim + 2
def spill : Expr := fullCapacity + (6 * tDim + nDim + 2 * qDim + 24)

theorem metadata_cells : metadata.cells = ∅ := fullCapacity_cells
theorem parents_cells : parents.cells = ∅ := by simp [parents, Expr.cells, metadata_cells, tDim]
theorem labels_cells : labels.cells = ∅ := by simp [labels, Expr.cells, metadata_cells, tDim, nDim]
theorem counts_cells : counts.cells = ∅ := by simp [counts, Expr.cells, labels_cells, tDim]
theorem header_cells : header.cells = ∅ := by simp [header, Expr.cells, counts_cells, tDim]
theorem goodFlags_cells : goodFlags.cells = ∅ := by simp [goodFlags, Expr.cells, header_cells]
theorem badFlags_cells : badFlags.cells = ∅ := by simp [badFlags, Expr.cells, goodFlags_cells, qDim]
theorem children_cells : children.cells = ∅ := by simp [children, Expr.cells, badFlags_cells, qDim]
theorem tool_cells : tool.cells = ∅ := by simp [tool, Expr.cells, children_cells, tDim]
theorem spill_cells : spill.cells = ∅ := by simp [spill, Expr.cells, fullCapacity_cells, tDim, nDim, qDim]

theorem metadata_eval (N q size : Nat) (env : Nat → Nat) : metadata.eval (dimensionROM N q size) env = PA17QueryLayout014.metadataBase N q size := rfl
theorem parents_eval (N q size : Nat) (env : Nat → Nat) : parents.eval (dimensionROM N q size) env = PA17QueryLayout014.parentBase N q size := rfl
theorem labels_eval (N q size : Nat) (env : Nat → Nat) : labels.eval (dimensionROM N q size) env = PA17QueryLayout014.labelBase N q size := rfl
theorem counts_eval (N q size : Nat) (env : Nat → Nat) : counts.eval (dimensionROM N q size) env = PA17QueryLayout014.countsBase N q size := rfl
theorem header_eval (N q size : Nat) (env : Nat → Nat) : header.eval (dimensionROM N q size) env = PA17QueryLayout014.header N q size := rfl
theorem goodFlags_eval (N q size : Nat) (env : Nat → Nat) : goodFlags.eval (dimensionROM N q size) env = PA17QueryLayout014.goodFlags N q size := rfl
theorem badFlags_eval (N q size : Nat) (env : Nat → Nat) : badFlags.eval (dimensionROM N q size) env = PA17QueryLayout014.badFlags N q size := rfl
theorem children_eval (N q size : Nat) (env : Nat → Nat) : children.eval (dimensionROM N q size) env = PA17QueryLayout014.childBase N q size := rfl
theorem tool_eval (N q size : Nat) (env : Nat → Nat) : tool.eval (dimensionROM N q size) env = PA17QueryLayout014.toolAddress N q size := rfl
theorem spill_eval (N q size : Nat) (env : Nat → Nat) : spill.eval (dimensionROM N q size) env = PA17WrappedNatRAM038a.spillBase N q size := rfl

def budgetProgram : Program := Program.sequence [PA17QueryTemplates044a.prepareProgram metadata labels counts,
  PA17QueryTemplates044b.headerProgram header,
  PA17QueryTemplates044c.testsProgram header counts parents (header + 1) goodFlags badFlags]

theorem budgetProgram_eval (N q size : Nat) (env : Nat → Nat) :
    budgetProgram.eval (dimensionROM N q size) env = PA17QueryBudget015.program N q size := by
  simp only [budgetProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [PA17QueryTemplates044a.prepareProgram_eval metadata labels counts metadata_cells labels_cells counts_cells,
    PA17QueryTemplates044b.headerProgram_eval header header_cells,
    PA17QueryTemplates044c.testsProgram_eval header counts parents (header + 1) goodFlags badFlags
      header_cells counts_cells parents_cells (by simp [Expr.cells, header_cells]) goodFlags_cells badFlags_cells,
    metadata_eval, labels_eval, counts_eval, header_eval, parents_eval, goodFlags_eval, badFlags_eval]
  simp only [Expr.eval, Binary.eval, header_eval, PA17QueryBudget015.program, PA17QueryLayout014.prepareProgram,
    PA17QueryBudget015.testsProgram, List.append_assoc]

def queryProgram : Program := Program.sequence [budgetProgram,
  PA17QueryTemplates044d.ranksProgram goodFlags badFlags header,
  PA17QueryTemplates044e.selectProgram counts labels header children,
  PA17QueryTemplates044d.replyProgram header tool]

theorem queryProgram_eval (N q size : Nat) (env : Nat → Nat) :
    queryProgram.eval (dimensionROM N q size) env = PA17Query019.program N q size := by
  simp only [queryProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [budgetProgram_eval,
    PA17QueryTemplates044d.ranksProgram_eval goodFlags badFlags header goodFlags_cells badFlags_cells,
    PA17QueryTemplates044e.selectProgram_eval counts labels header children counts_cells labels_cells children_cells,
    PA17QueryTemplates044d.replyProgram_eval, goodFlags_eval, badFlags_eval, header_eval,
    counts_eval, labels_eval, children_eval, tool_eval]
  simp only [PA17Query019.program, PA17Query019.ranksProgram, PA17Query019.selectProgram,
    PA17Query019.replyProgram, List.append_assoc]

theorem budgetProgram_uniformLength : budgetProgram.UniformLength := by
  exact ⟨PA17QueryTemplates044a.prepareProgram_uniformLength _ _ _,
    PA17QueryTemplates044b.headerProgram_uniformLength _, PA17QueryTemplates044c.testsProgram_uniformLength _ _ _ _ _ _, True.intro⟩

theorem queryProgram_uniformLength : queryProgram.UniformLength := by
  exact ⟨budgetProgram_uniformLength, PA17QueryTemplates044d.ranksProgram_uniformLength _ _ _,
    PA17QueryTemplates044e.selectProgram_uniformLength _ _ _ _, PA17QueryTemplates044d.replyProgram_uniformLength _ _, True.intro⟩

def wrappedQuery : Program := logicalProgram spill queryProgram

theorem wrappedQuery_eval (N q size : Nat) (env : Nat → Nat) :
    wrappedQuery.eval (dimensionROM N q size) env = PA17WrappedNatRAM038a.implementation.queryProgram N q size := by
  rw [wrappedQuery, logicalProgram_eval spill queryProgram (by simp [spill_cells]), spill_eval, queryProgram_eval]
  rfl

theorem wrappedQuery_uniformLength : wrappedQuery.UniformLength :=
  logicalProgram_uniformLength spill queryProgram queryProgram_uniformLength

theorem queryProgram_codeTemplate (N q size : Nat) (env : Nat → Nat) :
    queryProgram.codeTemplate.denote (dimensionROM N q size) env =
      (haltingWords (PA17Query019.program N q size)).length :: haltingWords (PA17Query019.program N q size) := by
  rw [Program.codeTemplate_denote _ _ _ queryProgram_uniformLength, queryProgram_eval]

theorem wrappedQuery_codeTemplate (N q size : Nat) (env : Nat → Nat) :
    wrappedQuery.codeTemplate.denote (dimensionROM N q size) env =
      (haltingWords (PA17WrappedNatRAM038a.implementation.queryProgram N q size)).length ::
        haltingWords (PA17WrappedNatRAM038a.implementation.queryProgram N q size) := by
  rw [Program.codeTemplate_denote _ _ _ wrappedQuery_uniformLength, wrappedQuery_eval]
end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044f
