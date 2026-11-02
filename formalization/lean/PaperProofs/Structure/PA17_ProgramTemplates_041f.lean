module
public import PaperProofs.Structure.PA17_ProgramTemplates_041e
public import PaperProofs.Structure.PA17_TerminalRow_002

/-! Actual copy/free-slot source templates. The control cell is lexical;
source, destination and length are runtime dimension expressions. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d

local instance pa17OfNat041f (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041f : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041f : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def copyBlock (source target index : Expr) : Program :=
  .code [.constant .address (source + index), .loadHeap .value .address,
    .constant .index (target + index), .storeHeap .index .value]

theorem copyBlock_eval (source target index : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (copyBlock source target index).eval rom environment =
      (IndexedCellRAM.copyBlock (source.eval rom environment) (target.eval rom environment)
        (index.eval rom environment)).map Op.base := by
  simp [copyBlock, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.storeHeap,
    IndexedCellRAM.copyBlock, Expr.eval, Binary.eval]

def copyProgram (source target count : Expr) : Program :=
  .repeat 18 count (copyBlock source target (count - .cell 18))

theorem copyProgram_eval (source target count : Expr)
    (hs : 18 ∉ source.cells) (ht : 18 ∉ target.cells) (hc : 18 ∉ count.cells)
    (rom : PhysicalROM) (environment : Nat → Nat) :
    (copyProgram source target count).eval rom environment =
      (IndexedCellRAM.copyWords (source.eval rom environment) (target.eval rom environment)
        (count.eval rom environment)).map Op.base := by
  rw [IndexedCellRAM.copyWords, IndexedCellRAM.copyIndices, List.map_flatMap]
  apply repeat_eval_ascending 18 count _ _ _ (count.eval rom environment) rfl
  intro index hi
  rw [copyBlock_eval]
  change (IndexedCellRAM.copyBlock
    (source.eval rom (Function.update environment 18 (count.eval rom environment - index)))
    (target.eval rom (Function.update environment 18 (count.eval rom environment - index)))
    (count.eval rom (Function.update environment 18 (count.eval rom environment - index)) -
      (count.eval rom environment - index))).map Op.base = _
  rw [eval_update_of_not_mem source rom environment 18 _ hs,
    eval_update_of_not_mem target rom environment 18 _ ht, eval_update_of_not_mem count rom environment 18 _ hc,
    Nat.sub_sub_self hi.le]

def setWord (target value : Expr) : Program :=
  .code [.constant .index target, .constant .value value, .storeHeap .index .value]

theorem setWord_eval (target value : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (setWord target value).eval rom environment =
      (IndexedCellRAM.constantBlock (target.eval rom environment) (value.eval rom environment)).map Op.base := by
  simp [setWord, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap, IndexedCellRAM.constantBlock]

def freeSlot (metadata target : Expr) : Program :=
  .append (copyProgram metadata (target + 1) tDim) (setWord target 1)

theorem freeSlot_eval (metadata target : Expr) (hs : 18 ∉ metadata.cells) (ht : 18 ∉ target.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (freeSlot metadata target).eval (dimensionROM N q size) environment =
      (IndexedCellRAM.copyWords (metadata.eval (dimensionROM N q size) environment)
        (target.eval (dimensionROM N q size) environment + 1) size).map Op.base ++
      (IndexedCellRAM.constantBlock (target.eval (dimensionROM N q size) environment) 1).map Op.base := by
  rw [freeSlot, Program.eval, copyProgram_eval _ _ _ hs (by
    change 18 ∉ target.cells ∪ ∅
    simpa only [Finset.union_empty] using ht) (by decide), setWord_eval]
  rfl

theorem setWord_uniformLength (target value : Expr) : (setWord target value).UniformLength := True.intro

theorem copyProgram_uniformLength (source target count : Expr) : (copyProgram source target count).UniformLength := by
  dsimp [copyProgram, Program.UniformLength, copyBlock, Program.lengthExpr, Expr.cells]
  decide

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
