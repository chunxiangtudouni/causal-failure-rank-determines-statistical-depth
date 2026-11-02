module
public import PaperProofs.Structure.PA17_ProgramTemplates_041j
public import PaperProofs.Structure.PA17_ProgramTemplates_041g
public import PaperProofs.Structure.PA17_ProgramTemplates_041h
public import PaperProofs.Structure.PA17_TableBuild_005

/-! Exact dimension-only template for the entire original full builder,
including metadata, all seed slots and reverse-stage positive-budget cells. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041k (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041k : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041k : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul041k : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def fullWork : Expr := (nDim + 1) * (qDim + 2) * (tDim + 1)
def fullAccumulator : Expr := fullWork + tDim + 1
def fullStageBase : Expr := fullCapacity + 3 * tDim + 1
def fullSlot (stage budget : Expr) : Expr := stage * (qDim + 2) + budget
def tableBase (slot : Expr) : Expr := slot * (tDim + 1)

theorem fullWork_cells : fullWork.cells = ∅ := by simp [fullWork, Expr.cells, nDim, qDim, tDim]
theorem fullAccumulator_cells : fullAccumulator.cells = ∅ := by simp [fullAccumulator, Expr.cells, fullWork_cells, tDim]
theorem fullStageBase_cells : fullStageBase.cells = ∅ := by simp [fullStageBase, Expr.cells, fullCapacity_cells, tDim]

def fullCell (stage budget : Expr) : Program :=
  Program.sequence [toTagLast (tableBase (fullSlot (stage + 1) (budget - 1))) fullWork,
    kernel fullWork (tableBase (fullSlot (stage + 1) budget)) fullAccumulator
      (fullCapacity + tDim) (fullStageBase + stage),
    toTagFirst fullWork (tableBase (fullSlot stage budget))]

theorem fullCell_eval (stage budget : Expr)
    (hs18 : 18 ∉ stage.cells) (hb18 : 18 ∉ budget.cells)
    (hs20 : 20 ∉ stage.cells) (hb20 : 20 ∉ budget.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (fullCell stage budget).eval (dimensionROM N q size) environment =
      PA17TableBuild005.cellProgram N q size (stage.eval (dimensionROM N q size) environment)
        (budget.eval (dimensionROM N q size) environment) := by
  have hf18 : 18 ∉ fullWork.cells := by simp [fullWork_cells]
  have hf20 : 20 ∉ fullWork.cells := by simp [fullWork_cells]
  have ha20 : 20 ∉ fullAccumulator.cells := by simp [fullAccumulator_cells]
  have hg20 : 20 ∉ (tableBase (fullSlot (stage + 1) budget)).cells := by
    simp [tableBase, fullSlot, Expr.cells, qDim, tDim, hs20, hb20]
  have hp20 : 20 ∉ (fullCapacity + tDim).cells := by simp [Expr.cells, fullCapacity_cells, tDim]
  have hbsub : 18 ∉ (budget - 1 : Expr).cells := by
    change 18 ∉ budget.cells ∪ ∅
    simpa only [Finset.union_empty] using hb18
  have hb : 18 ∉ (tableBase (fullSlot (stage + 1) (budget - 1))).cells := by
    simp [tableBase, fullSlot, Expr.cells, qDim, tDim, hs18, hbsub]
  have ho : 18 ∉ (tableBase (fullSlot stage budget)).cells := by
    simp [tableBase, fullSlot, Expr.cells, qDim, tDim, hs18, hb18]
  simp only [fullCell, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [toTagLast_eval _ _ hb hf18, kernel_eval _ _ _ _ _ hf20 hg20 ha20 hp20,
    toTagFirst_eval _ _ hf18 ho]
  simp only [PA17TableBuild005.cellProgram, PA17TableCell004.program, PA17CellLayout003.kernelProgram,
    List.append_assoc]
  rfl

def fullSeeds : Program :=
  .append
    (.repeat 16 (nDim + 1)
      (freeSlot fullCapacity (tableBase (fullSlot (nDim + 1 - .cell 16) 0))))
    (.repeat 17 (qDim + 2)
      (freeSlot fullCapacity (tableBase (fullSlot nDim (qDim + 2 - .cell 17)))))

theorem fullSeeds_eval (N q size : Nat) (environment : Nat → Nat) :
    fullSeeds.eval (dimensionROM N q size) environment =
      PA17TerminalRow002.freeSlots size (PA17CellLayout003.capacityWords N q size)
        (PA17TerminalRow002.seedSlots N q) := by
  have hfirst : (Program.repeat 16 (nDim + 1)
      (freeSlot fullCapacity (tableBase (fullSlot (nDim + 1 - .cell 16) 0)))).eval
      (dimensionROM N q size) environment = (List.range (N + 1)).flatMap
      (fun stage => PA17TerminalRow002.writeFreeSlot size (PA17CellLayout003.capacityWords N q size) (stage * (q + 2))) := by
    apply repeat_eval_ascending 16 (nDim + 1) _ _ _ (N + 1) rfl
    intro stage hs
    rw [freeSlot_eval _ _ (by simp [fullCapacity_cells]) (by decide)]
    change (IndexedCellRAM.copyWords (PA17CellLayout003.capacityWords N q size)
        ((((N + 1 - (N + 1 - stage)) * (q + 2) + 0) * (size + 1)) + 1) size).map Op.base ++
      (IndexedCellRAM.constantBlock (((N + 1 - (N + 1 - stage)) * (q + 2) + 0) * (size + 1)) 1).map Op.base = _
    rw [Nat.sub_sub_self hs.le]
    rfl
  have hsecond : (Program.repeat 17 (qDim + 2)
      (freeSlot fullCapacity (tableBase (fullSlot nDim (qDim + 2 - .cell 17))))).eval
      (dimensionROM N q size) environment = (List.range (q + 2)).flatMap
      (fun budget => PA17TerminalRow002.writeFreeSlot size (PA17CellLayout003.capacityWords N q size) (N * (q + 2) + budget)) := by
    apply repeat_eval_ascending 17 (qDim + 2) _ _ _ (q + 2) rfl
    intro budget hb
    rw [freeSlot_eval _ _ (by simp [fullCapacity_cells]) (by decide)]
    change (IndexedCellRAM.copyWords (PA17CellLayout003.capacityWords N q size)
        ((N * (q + 2) + (q + 2 - (q + 2 - budget))) * (size + 1) + 1) size).map Op.base ++
      (IndexedCellRAM.constantBlock ((N * (q + 2) + (q + 2 - (q + 2 - budget))) * (size + 1)) 1).map Op.base = _
    rw [Nat.sub_sub_self hb.le]
    rfl
  rw [fullSeeds, Program.eval, hfirst, hsecond]
  simp only [PA17TerminalRow002.freeSlots, PA17TerminalRow002.seedSlots, List.flatMap_append, List.flatMap_map]

def fullPrepare : Program :=
  Program.sequence [metadataProgram fullCapacity, stageProgram fullStageBase, fullSeeds]

theorem fullPrepare_eval (N q size : Nat) (environment : Nat → Nat) :
    fullPrepare.eval (dimensionROM N q size) environment = PA17TablePrepare004.program N q size := by
  simp only [fullPrepare, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [metadataProgram_eval _ fullCapacity_cells, fullCapacity_eval,
    stageProgram_eval _ fullStageBase_cells, fullSeeds_eval]
  exact List.append_assoc _ _ _ |>.symm

def fullRow (stage : Expr) : Program :=
  .repeat 17 (qDim + 1) (fullCell stage (qDim + 1 - .cell 17 + 1))

theorem fullRow_eval (stage : Expr) (h17 : 17 ∉ stage.cells) (h18 : 18 ∉ stage.cells) (h20 : 20 ∉ stage.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (fullRow stage).eval (dimensionROM N q size) environment =
      PA17RowSchedule004.rowProgram (PA17TableBuild005.cellProgram N q size) q
        (stage.eval (dimensionROM N q size) environment) := by
  rw [PA17RowSchedule004.rowProgram, PA17RowSchedule004.positiveBudgets, List.flatMap_map]
  apply repeat_eval_ascending 17 (qDim + 1) _ _ _ (q + 1) rfl
  intro budget hb
  rw [fullCell_eval _ _ h18 (by decide) h20 (by decide)]
  change PA17TableBuild005.cellProgram N q size
    (stage.eval (dimensionROM N q size) (Function.update environment 17 (q + 1 - budget)))
    (q + 1 - (q + 1 - budget) + 1) = _
  rw [eval_update_of_not_mem stage _ environment 17 _ h17, Nat.sub_sub_self hb.le]

def fullBuild : Program := .append fullPrepare (.repeat 16 nDim (fullRow (.cell 16 - 1)))

theorem fullBuild_eval (N q size : Nat) (environment : Nat → Nat) :
    fullBuild.eval (dimensionROM N q size) environment = PA17TableBuild005.buildProgram N q size := by
  have hloop : (Program.repeat 16 nDim (fullRow (.cell 16 - 1))).eval (dimensionROM N q size) environment =
      PA17RowSchedule004.scheduleProgram (PA17TableBuild005.cellProgram N q size) N q := by
    apply repeat_eval_descending 16 nDim _ _ _ N rfl
    intro stage _
    rw [fullRow_eval _ (by decide) (by decide) (by decide)]
    change PA17RowSchedule004.rowProgram (PA17TableBuild005.cellProgram N q size) q (stage + 1 - 1) = _
    rw [Nat.add_sub_cancel]
  rw [fullBuild, Program.eval, fullPrepare_eval, hloop]
  rfl

theorem fullCell_uniformLength (stage budget : Expr) : (fullCell stage budget).UniformLength := by
  exact ⟨toTagLast_uniformLength _ _, kernel_uniformLength _ _ _ _ _, toTagFirst_uniformLength _ _, True.intro⟩

theorem fullBuild_uniformLength : fullBuild.UniformLength := by
  dsimp [fullBuild, fullPrepare, fullSeeds, fullRow, fullCell, fullSlot, tableBase,
    toTagFirst, toTagLast, copyProgram, copyBlock, freeSlot, setWord,
    kernel, extension, extensionInit, extensionTail, ancestorBlock, minimumPass, minimumNode,
    normalize, normalizeNode, clearWord, minimumTag, metadataProgram, metadataClear,
    metadataNode, metadataBit, metadataTail, stageProgram, stageBlock, stageNode,
    stageNodeTail, stageBit, stageSave, Program.sequence, Program.UniformLength,
    Program.lengthExpr, Expr.cells, nDim, qDim, tDim]
  simp only [Finset.union_empty, Finset.notMem_empty, not_false_eq_true, and_self]

theorem fullBuild_codeTemplate (N q size : Nat) (environment : Nat → Nat) :
    fullBuild.codeTemplate.denote (dimensionROM N q size) environment =
      (haltingWords (PA17TableBuild005.buildProgram N q size)).length ::
        haltingWords (PA17TableBuild005.buildProgram N q size) := by
  rw [Program.codeTemplate_denote _ _ _ fullBuild_uniformLength, fullBuild_eval]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
