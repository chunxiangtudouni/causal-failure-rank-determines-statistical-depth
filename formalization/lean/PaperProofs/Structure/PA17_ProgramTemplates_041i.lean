module
public import PaperProofs.Structure.PA17_ProgramTemplates_041f
public import PaperProofs.Structure.PA17_UniformCell_002

/-! Actual tag copies and bottom-up normalization templates. Every emitted
instruction is from the original program; only dimension immediates vary. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041i (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041i : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041i : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def toTagFirst (source target : Expr) : Program :=
  .append (copyProgram source (target + 1) tDim) (copyProgram (source + tDim) target 1)

def toTagLast (source target : Expr) : Program :=
  .append (copyProgram (source + 1) target tDim) (copyProgram source (target + tDim) 1)

theorem toTagFirst_eval (source target : Expr) (hs : 18 ∉ source.cells) (ht : 18 ∉ target.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (toTagFirst source target).eval (dimensionROM N q size) environment =
      PA17TagBridge001.toTagFirst size (source.eval (dimensionROM N q size) environment)
        (target.eval (dimensionROM N q size) environment) := by
  rw [toTagFirst, Program.eval, copyProgram_eval _ _ _ hs (by simpa [Expr.cells] using ht) (by decide),
    copyProgram_eval _ _ _ (by simpa [Expr.cells, tDim] using hs) ht (by decide)]
  simp only [PA17TagBridge001.toTagFirst, List.map_append]
  rfl

theorem toTagLast_eval (source target : Expr) (hs : 18 ∉ source.cells) (ht : 18 ∉ target.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (toTagLast source target).eval (dimensionROM N q size) environment =
      PA17TagBridge001.toTagLast size (source.eval (dimensionROM N q size) environment)
        (target.eval (dimensionROM N q size) environment) := by
  rw [toTagLast, Program.eval, copyProgram_eval _ _ _ (by simpa [Expr.cells] using hs) ht (by decide),
    copyProgram_eval _ _ _ hs (by simpa [Expr.cells, tDim] using ht) (by decide)]
  simp only [PA17TagBridge001.toTagLast, List.map_append]
  rfl

def clearWord (target : Expr) : Program := setWord target 0

theorem clearWord_eval (target : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (clearWord target).eval rom environment =
      UniformNormalizationRAM.clearBlock (target.eval rom environment) := by
  rw [clearWord, setWord_eval]
  rfl

def normalizeNode (capacity accumulator node : Expr) : Program :=
  .code [.constant .index (tDim + node), .loadROM .internal .flag .index,
    .constant .address (accumulator + node + 1), .loadHeap .total .address,
    .constant .index (capacity + node), .loadHeap .old .index,
    .minimum .fresh .old .total, .select .fresh .flag .fresh .old, .storeHeap .index .fresh,
    .constant .index node, .loadROM .internal .index .index,
    .constant .address accumulator, .add .address .address .index,
    .loadHeap .total .address, .add .total .total .fresh, .storeHeap .address .total]

theorem normalizeNode_eval (capacity accumulator node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (normalizeNode capacity accumulator node).eval (dimensionROM N q size) environment =
      UniformNormalizationRAM.nodeBlock size (capacity.eval (dimensionROM N q size) environment)
        (accumulator.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  simp [normalizeNode, Program.eval, instructions, OpExpr.eval, OpExpr.loadROM, OpExpr.loadHeap,
    OpExpr.minimum, OpExpr.select, OpExpr.storeHeap, OpExpr.add, UniformNormalizationRAM.nodeBlock,
    UniformNormalizationRAM.updateNode, UniformNormalizationRAM.pushParent, Expr.eval, Binary.eval,
    tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def normalize (capacity accumulator : Expr) : Program :=
  .append (.repeat 20 (tDim + 1) (clearWord (accumulator + (tDim + 1 - .cell 20))))
    (.repeat 20 tDim (normalizeNode capacity accumulator (tDim - .cell 20)))

theorem normalize_eval (capacity accumulator : Expr)
    (hc : 20 ∉ capacity.cells) (ha : 20 ∉ accumulator.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (normalize capacity accumulator).eval (dimensionROM N q size) environment =
      UniformNormalizationRAM.program size (capacity.eval (dimensionROM N q size) environment)
        (accumulator.eval (dimensionROM N q size) environment) := by
  have hclear : (Program.repeat 20 (tDim + 1)
      (clearWord (accumulator + (tDim + 1 - .cell 20)))).eval (dimensionROM N q size) environment =
      UniformNormalizationRAM.clearWords (accumulator.eval (dimensionROM N q size) environment) (size + 1) := by
    apply repeat_eval_ascending 20 (tDim + 1) _ _ _ (size + 1) rfl
    intro index hi
    rw [clearWord_eval]
    change UniformNormalizationRAM.clearBlock
      (accumulator.eval (dimensionROM N q size) (Function.update environment 20 (size + 1 - index)) +
        (size + 1 - (size + 1 - index))) = _
    rw [eval_update_of_not_mem accumulator _ environment 20 _ ha, Nat.sub_sub_self hi.le]
  have hnodes : (Program.repeat 20 tDim (normalizeNode capacity accumulator (tDim - .cell 20))).eval
      (dimensionROM N q size) environment = (List.range size).flatMap
      (UniformNormalizationRAM.nodeBlock size (capacity.eval (dimensionROM N q size) environment)
        (accumulator.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 20 tDim _ _ _ size rfl
    intro index hi
    rw [normalizeNode_eval]
    change UniformNormalizationRAM.nodeBlock size
      (capacity.eval (dimensionROM N q size) (Function.update environment 20 (size - index)))
      (accumulator.eval (dimensionROM N q size) (Function.update environment 20 (size - index)))
      (size - (size - index)) = _
    rw [eval_update_of_not_mem capacity _ environment 20 _ hc,
      eval_update_of_not_mem accumulator _ environment 20 _ ha, Nat.sub_sub_self hi.le]
  rw [normalize, Program.eval, hclear, hnodes]
  rfl

theorem toTagFirst_uniformLength (source target : Expr) : (toTagFirst source target).UniformLength :=
  ⟨copyProgram_uniformLength _ _ _, copyProgram_uniformLength _ _ _⟩

theorem toTagLast_uniformLength (source target : Expr) : (toTagLast source target).UniformLength :=
  ⟨copyProgram_uniformLength _ _ _, copyProgram_uniformLength _ _ _⟩

theorem normalize_uniformLength (capacity accumulator : Expr) : (normalize capacity accumulator).UniformLength := by
  dsimp [normalize, clearWord, setWord, normalizeNode, Program.UniformLength, Program.lengthExpr, Expr.cells]
  decide

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
