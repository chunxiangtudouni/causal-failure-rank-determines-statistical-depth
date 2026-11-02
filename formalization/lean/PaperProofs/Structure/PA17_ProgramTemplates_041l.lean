module
public import PaperProofs.Structure.PA17_ProgramTemplates_041k
public import PaperProofs.Structure.PA17_Rolling_018

/-! Actual two-row builder template. Parity is computed by subtraction and
division expressions; stage incidence and every row/cell are really emitted. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041l (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041l : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041l : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul041l : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def rollingSlot (stage budget : Expr) : Expr :=
  (stage - (.binary .divide stage 2) * 2) * (qDim + 2) + budget
def rollingWork : Expr := 2 * (qDim + 2) * (tDim + 1)
def rollingAccumulator : Expr := rollingWork + tDim + 1
def rollingCapacity : Expr := rollingWork + 2 * (tDim + 1)
def rollingStageWord : Expr := rollingCapacity + 3 * tDim + 1

theorem rollingSlot_eval (stage budget : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (rollingSlot stage budget).eval (dimensionROM N q size) environment =
      PA17Rolling018.slot q (stage.eval (dimensionROM N q size) environment)
        (budget.eval (dimensionROM N q size) environment) := by
  let value := stage.eval (dimensionROM N q size) environment
  change (value - (value / 2) * 2) * (q + 2) + _ = (value % 2) * (q + 2) + _
  have hp : value - (value / 2) * 2 = value % 2 := by omega
  rw [hp]

theorem rollingWork_cells : rollingWork.cells = ∅ := by simp [rollingWork, Expr.cells, qDim, tDim]
theorem rollingAccumulator_cells : rollingAccumulator.cells = ∅ := by
  simp [rollingAccumulator, Expr.cells, rollingWork_cells, tDim]
theorem rollingCapacity_cells : rollingCapacity.cells = ∅ := by
  simp [rollingCapacity, Expr.cells, rollingWork_cells, tDim]
theorem rollingStageWord_cells : rollingStageWord.cells = ∅ := by
  simp [rollingStageWord, Expr.cells, rollingCapacity_cells, tDim]

def rollingCell (stage budget : Expr) : Program :=
  Program.sequence [toTagLast (tableBase (rollingSlot (stage + 1) (budget - 1))) rollingWork,
    kernel rollingWork (tableBase (rollingSlot (stage + 1) budget)) rollingAccumulator
      (rollingCapacity + tDim) rollingStageWord,
    toTagFirst rollingWork (tableBase (rollingSlot stage budget))]

theorem rollingCell_eval (stage budget : Expr)
    (hs18 : 18 ∉ stage.cells) (hb18 : 18 ∉ budget.cells)
    (hs20 : 20 ∉ stage.cells) (hb20 : 20 ∉ budget.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (rollingCell stage budget).eval (dimensionROM N q size) environment =
      PA17Rolling018.cellProgram q size (stage.eval (dimensionROM N q size) environment)
        (budget.eval (dimensionROM N q size) environment) := by
  have hf18 : 18 ∉ rollingWork.cells := by simp [rollingWork_cells]
  have hf20 : 20 ∉ rollingWork.cells := by simp [rollingWork_cells]
  have ha20 : 20 ∉ rollingAccumulator.cells := by simp [rollingAccumulator_cells]
  have hp20 : 20 ∉ (rollingCapacity + tDim).cells := by simp [Expr.cells, rollingCapacity_cells, tDim]
  have hbsub : 18 ∉ (budget - 1 : Expr).cells := by
    change 18 ∉ budget.cells ∪ ∅
    simpa only [Finset.union_empty] using hb18
  have hslots (counter : Nat) (s b : Expr) (hs : counter ∉ s.cells) (hb : counter ∉ b.cells) :
      counter ∉ (tableBase (rollingSlot s b)).cells := by
    change counter ∉ ((s.cells ∪ ((s.cells ∪ ∅) ∪ ∅)) ∪ (∅ ∪ ∅) ∪ b.cells) ∪ (∅ ∪ ∅)
    simp only [Finset.union_empty, Finset.mem_union, not_or] at *
    exact ⟨⟨hs, hs⟩, hb⟩
  have hs18' : 18 ∉ (stage + 1 : Expr).cells := by simpa [Expr.cells] using hs18
  have hs20' : 20 ∉ (stage + 1 : Expr).cells := by simpa [Expr.cells] using hs20
  simp only [rollingCell, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [toTagLast_eval _ _ (hslots 18 _ _ hs18' hbsub) hf18,
    kernel_eval _ _ _ _ _ hf20 (hslots 20 _ _ hs20' hb20) ha20 hp20,
    toTagFirst_eval _ _ hf18 (hslots 18 _ _ hs18 hb18)]
  have hbase (slot : Expr) : (tableBase slot).eval (dimensionROM N q size) environment =
      PA17Rolling018.base size (slot.eval (dimensionROM N q size) environment) := rfl
  simp only [hbase, rollingSlot_eval]
  simp only [PA17Rolling018.cellProgram, PA17Rolling018.kernelProgram, List.append_assoc]
  rfl

def saveCurrent (target : Expr) : Program := .code [.constant .index target, .storeHeap .index .value]

theorem saveCurrent_eval (target : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (saveCurrent target).eval rom environment = PA17Rolling018.saveValue (target.eval rom environment) := by
  rfl

def rollingStage (stage : Expr) : Program :=
  Program.sequence [.code [.constant .value 0], .repeat 18 tDim (stageNode stage (tDim - .cell 18)),
    saveCurrent rollingStageWord]

theorem rollingStage_eval (stage : Expr) (h18 : 18 ∉ stage.cells) (h19 : 19 ∉ stage.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (rollingStage stage).eval (dimensionROM N q size) environment =
      PA17Rolling018.stageProgram N q size (stage.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 18 tDim (stageNode stage (tDim - .cell 18))).eval
      (dimensionROM N q size) environment = (List.range size).flatMap
      (PA17StageMap001.nodeBlock N q (stage.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 18 tDim _ _ _ size rfl
    intro node hn
    rw [stageNode_eval _ _ h19 (by decide)]
    change PA17StageMap001.nodeBlock N q
      (stage.eval (dimensionROM N q size) (Function.update environment 18 (size - node))) (size - (size - node)) = _
    rw [eval_update_of_not_mem stage _ environment 18 _ h18, Nat.sub_sub_self hn.le]
  simp only [rollingStage, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, saveCurrent_eval]
  exact List.append_assoc _ _ _ |>.symm

def rollingPrepare : Program :=
  .append (metadataProgram rollingCapacity)
    (.repeat 17 (2 * (qDim + 2))
      (freeSlot rollingCapacity (tableBase (2 * (qDim + 2) - .cell 17))))

theorem rollingPrepare_eval (N q size : Nat) (environment : Nat → Nat) :
    rollingPrepare.eval (dimensionROM N q size) environment = PA17Rolling018.prepareProgram N q size := by
  have hloop : (Program.repeat 17 (2 * (qDim + 2))
      (freeSlot rollingCapacity (tableBase (2 * (qDim + 2) - .cell 17)))).eval
      (dimensionROM N q size) environment = (List.range (2 * (q + 2))).flatMap
      (PA17Rolling018.freeSlot q size) := by
    apply repeat_eval_ascending 17 (2 * (qDim + 2)) _ _ _ (2 * (q + 2)) rfl
    intro slot hs
    rw [freeSlot_eval _ _ (by simp [rollingCapacity_cells]) (by decide)]
    change (IndexedCellRAM.copyWords (PA17Rolling018.metadataBase q size)
        ((2 * (q + 2) - (2 * (q + 2) - slot)) * (size + 1) + 1) size).map Op.base ++
      (IndexedCellRAM.constantBlock ((2 * (q + 2) - (2 * (q + 2) - slot)) * (size + 1)) 1).map Op.base = _
    rw [Nat.sub_sub_self hs.le]
    rfl
  rw [rollingPrepare, Program.eval, metadataProgram_eval _ rollingCapacity_cells, hloop]
  rfl

def rollingRow (stage : Expr) : Program :=
  .append (rollingStage stage)
    (.repeat 17 (qDim + 1) (rollingCell stage (qDim + 1 - .cell 17 + 1)))

theorem rollingRow_eval (stage : Expr)
    (h17 : 17 ∉ stage.cells) (h18 : 18 ∉ stage.cells) (h19 : 19 ∉ stage.cells) (h20 : 20 ∉ stage.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (rollingRow stage).eval (dimensionROM N q size) environment =
      PA17Rolling018.rowProgram N q size (stage.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 17 (qDim + 1) (rollingCell stage (qDim + 1 - .cell 17 + 1))).eval
      (dimensionROM N q size) environment = (PA17Rolling018.positiveBudgets q).flatMap
      (PA17Rolling018.cellProgram q size (stage.eval (dimensionROM N q size) environment)) := by
    rw [PA17Rolling018.positiveBudgets, List.flatMap_map]
    apply repeat_eval_ascending 17 (qDim + 1) _ _ _ (q + 1) rfl
    intro budget hb
    rw [rollingCell_eval _ _ h18 (by decide) h20 (by decide)]
    change PA17Rolling018.cellProgram q size
      (stage.eval (dimensionROM N q size) (Function.update environment 17 (q + 1 - budget)))
      (q + 1 - (q + 1 - budget) + 1) = _
    rw [eval_update_of_not_mem stage _ environment 17 _ h17, Nat.sub_sub_self hb.le]
  rw [rollingRow, Program.eval, rollingStage_eval _ h18 h19, hloop]
  rfl

def rollingBuild : Program := .append rollingPrepare (.repeat 16 nDim (rollingRow (.cell 16 - 1)))

theorem rollingBuild_eval (N q size : Nat) (environment : Nat → Nat) :
    rollingBuild.eval (dimensionROM N q size) environment = PA17Rolling018.buildProgram N q size := by
  have hloop : (Program.repeat 16 nDim (rollingRow (.cell 16 - 1))).eval (dimensionROM N q size) environment =
      PA17Rolling018.scheduleProgram N q size N := by
    apply repeat_eval_descending 16 nDim _ _ _ N rfl
    intro stage _
    rw [rollingRow_eval _ (by decide) (by decide) (by decide) (by decide)]
    change PA17Rolling018.rowProgram N q size (stage + 1 - 1) = _
    rw [Nat.add_sub_cancel]
  rw [rollingBuild, Program.eval, rollingPrepare_eval, hloop]
  rfl

theorem rollingBuild_uniformLength : rollingBuild.UniformLength := by
  dsimp [rollingBuild, rollingPrepare, rollingRow, rollingStage, rollingCell, rollingSlot, tableBase,
    toTagFirst, toTagLast, copyProgram, copyBlock, freeSlot, setWord, saveCurrent,
    kernel, extension, extensionInit, extensionTail, ancestorBlock, minimumPass, minimumNode,
    normalize, normalizeNode, clearWord, minimumTag, metadataProgram, metadataClear,
    metadataNode, metadataBit, metadataTail, stageNode, stageNodeTail, stageBit,
    Program.sequence, Program.UniformLength, Program.lengthExpr, Expr.cells, nDim, qDim, tDim]
  simp only [Finset.union_empty, Finset.notMem_empty, not_false_eq_true, and_self]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
