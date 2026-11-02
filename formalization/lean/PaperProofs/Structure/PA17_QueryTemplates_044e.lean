module
public import PaperProofs.Structure.PA17_QueryTemplates_044d
public import PaperProofs.Structure.PA17_QuerySelection_010b

/-! Actual finite selector AST: prelude, clearing, reverse parent push,
fixed-fuel first-child descent, and masking. No table payload is compiled in. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044e
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041
local instance pa17OfNat044e (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add044e : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub044e : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def clearBlock (address : Expr) : Program := .code [
  .constant .index address, .constant .value 0, .storeHeap .index .value]

theorem clearBlock_eval (address : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (clearBlock address).eval rom env = UniformNormalizationRAM.clearBlock (address.eval rom env) := by
  simp [clearBlock, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap, UniformNormalizationRAM.clearBlock, Expr.eval]

def clearProgram (base : Expr) : Program := .repeat 18 (tDim + 1) (clearBlock (base + (tDim + 1 - .cell 18)))

theorem clearProgram_eval (base : Expr) (hb : base.cells = ∅) (N q size : Nat) (env : Nat → Nat) :
    (clearProgram base).eval (dimensionROM N q size) env = UniformNormalizationRAM.clearWords
      (base.eval (dimensionROM N q size) env) (size + 1) := by
  apply repeat_eval_ascending 18 (tDim + 1) _ _ _ (size + 1) rfl
  intro index hi
  rw [clearBlock_eval]
  change UniformNormalizationRAM.clearBlock (base.eval _ (Function.update env 18 (size + 1 - index)) +
    (size + 1 - (size + 1 - index))) = _
  rw [eval_update_of_not_mem base _ env 18 _ (by simp [hb]), Nat.sub_sub_self hi.le]

def parentBlock (counts pointer children node : Expr) : Program := .code [
  .constant .index (counts + node), .loadHeap .old .index,
  .constant .index pointer, .loadHeap .address .index,
  .constant .fresh node, .add .address .address .fresh, .loadHeap .fresh .address,
  .subtract .flag .fresh .old, .constant .index node, .loadROM .internal .total .index,
  .constant .index children, .add .index .index .total, .loadHeap .old .index,
  .constant .fresh (node + 1), .select .value .flag .fresh .old,
  .select .value .total .value .old, .storeHeap .index .value]

theorem parentBlock_eval (counts pointer children node : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (parentBlock counts pointer children node).eval rom env = PA17QuerySelection010.parentBlock
      (counts.eval rom env) (pointer.eval rom env) (children.eval rom env) (node.eval rom env) := by
  simp [parentBlock, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.loadROM,
    OpExpr.add, OpExpr.subtract, OpExpr.select, OpExpr.storeHeap, Expr.eval, Binary.eval,
    PA17QuerySelection010.parentBlock]

def parentsProgram (counts pointer children : Expr) : Program := .append (clearProgram children)
  (.repeat 18 tDim (parentBlock counts pointer children (.cell 18 - 1)))

theorem parentsProgram_eval (counts pointer children : Expr) (hc : counts.cells = ∅)
    (hp : pointer.cells = ∅) (hk : children.cells = ∅) (N q size : Nat) (env : Nat → Nat) :
    (parentsProgram counts pointer children).eval (dimensionROM N q size) env = PA17QuerySelection010.program size
      (counts.eval (dimensionROM N q size) env) (pointer.eval (dimensionROM N q size) env) (children.eval (dimensionROM N q size) env) := by
  have hh : (Program.repeat 18 tDim (parentBlock counts pointer children (.cell 18 - 1))).eval (dimensionROM N q size) env =
      (List.range size).reverse.flatMap (PA17QuerySelection010.parentBlock
        (counts.eval (dimensionROM N q size) env) (pointer.eval (dimensionROM N q size) env) (children.eval (dimensionROM N q size) env)) := by
    apply repeat_eval_descending 18 tDim _ _ _ size rfl
    intro index _
    rw [parentBlock_eval]
    change PA17QuerySelection010.parentBlock
      (counts.eval _ (Function.update env 18 (index + 1))) (pointer.eval _ (Function.update env 18 (index + 1)))
      (children.eval _ (Function.update env 18 (index + 1))) (index + 1 - 1) = _
    rw [eval_update_of_not_mem counts _ env 18 _ (by simp [hc]),
      eval_update_of_not_mem pointer _ env 18 _ (by simp [hp]),
      eval_update_of_not_mem children _ env 18 _ (by simp [hk]), Nat.add_sub_cancel]
  rw [parentsProgram, Program.eval, clearProgram_eval children hk, hh]
  rfl

def descentBlock (labels children : Expr) : Program := .code [
  .subtract .index .address .total, .constant .old labels, .add .index .old .index, .loadHeap .flag .index,
  .constant .old 0, .select .flag .address .flag .old, .select .value .flag .flag .value,
  .constant .index children, .add .index .index .address, .loadHeap .fresh .index,
  .select .address .flag .old .fresh]

theorem descentBlock_eval (labels children : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (descentBlock labels children).eval rom env = PA17QuerySelection010b.block (labels.eval rom env) (children.eval rom env) := by
  simp [descentBlock, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.subtract,
    OpExpr.add, OpExpr.select, PA17QuerySelection010b.block, Expr.eval]

def descentLoop (labels children : Expr) : Program := .repeat 20 tDim (descentBlock labels children)

theorem descentLoop_eval (labels children : Expr) (hl : labels.cells = ∅) (hc : children.cells = ∅)
    (N q size : Nat) (env : Nat → Nat) :
    (descentLoop labels children).eval (dimensionROM N q size) env = PA17QuerySelection010b.loop
      (labels.eval (dimensionROM N q size) env) (children.eval (dimensionROM N q size) env) size := by
  apply PA17QueryTemplates044c.repeat_eval_block 20 tDim _ _ _ size _ rfl
  intro index _
  rw [descentBlock_eval, eval_update_of_not_mem labels _ env 20 _ (by simp [hl]),
    eval_update_of_not_mem children _ env 20 _ (by simp [hc])]

def preludeStart (head : Expr) : Program := .code [
  .constant .index head, .loadHeap .address .index, .constant .index (head + 6), .loadHeap .value .index]
def preludeTail (pointer : Expr) : Program := .code [
  .constant .old 1, .add .address .address .old, .constant .index pointer, .storeHeap .index .address]

theorem preludeStart_eval (head : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (preludeStart head).eval rom env = PA17QuerySelection010b.preludeStart (head.eval rom env) := by
  simp [preludeStart, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, Expr.eval, Binary.eval,
    PA17QuerySelection010b.preludeStart]
theorem preludeTail_eval (pointer : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (preludeTail pointer).eval rom env = PA17QuerySelection010b.preludeTail (pointer.eval rom env) := by
  simp [preludeTail, Program.eval, instructions, OpExpr.eval, OpExpr.add, OpExpr.storeHeap, Expr.eval,
    PA17QuerySelection010b.preludeTail]

def prelude (head pointer : Expr) : Program := Program.sequence [preludeStart head,
  .repeat 20 (tDim + 1) (.code [.literal (.base (.add .address .address .value))]), preludeTail pointer]

theorem prelude_eval (head pointer : Expr) (N q size : Nat) (env : Nat → Nat) :
    (prelude head pointer).eval (dimensionROM N q size) env = PA17QuerySelection010b.prelude size
      (head.eval (dimensionROM N q size) env) (pointer.eval (dimensionROM N q size) env) := by
  simp only [prelude, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [preludeStart_eval, repeat_eval_replicate 20 (tDim + 1) _ _ _ (size + 1) rfl, preludeTail_eval]
  rfl

def descentInit (head : Expr) : Program := .code [
  .constant .index (head + 1), .loadHeap .address .index, .constant .total 1, .constant .value 0]
theorem descentInit_eval (head : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (descentInit head).eval rom env = PA17QuerySelection010b.descentInit (head.eval rom env) := by
  simp [descentInit, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, Expr.eval, Binary.eval,
    PA17QuerySelection010b.descentInit]

def finish (head pointer tool : Expr) : Program := .code [
  .constant .index pointer, .loadHeap .fresh .index, .subtract .index .fresh .total,
  .loadHeap .flag .index, .constant .old 0, .select .value .flag .value .old,
  .constant .index (head + 7), .loadHeap .flag .index, .select .value .flag .value .old,
  .constant .index tool, .storeHeap .index .value, .add .index .value .old]
theorem finish_eval (head pointer tool : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (finish head pointer tool).eval rom env = PA17QuerySelection010b.finish (head.eval rom env)
      (pointer.eval rom env) (tool.eval rom env) := by
  simp [finish, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.storeHeap,
    OpExpr.subtract, OpExpr.select, OpExpr.add, Expr.eval, Binary.eval, PA17QuerySelection010b.finish]

def selectProgram (counts labels head children : Expr) : Program := Program.sequence [
  prelude head (children + tDim + 1), parentsProgram counts (children + tDim + 1) children,
  descentInit head, descentLoop labels children, finish head (children + tDim + 1) (children + tDim + 2)]

theorem selectProgram_eval (counts labels head children : Expr) (hc : counts.cells = ∅)
    (hl : labels.cells = ∅) (hk : children.cells = ∅) (N q size : Nat) (env : Nat → Nat) :
    (selectProgram counts labels head children).eval (dimensionROM N q size) env = PA17QuerySelection010b.program size
      (counts.eval (dimensionROM N q size) env) (labels.eval (dimensionROM N q size) env)
      (head.eval (dimensionROM N q size) env) (children.eval (dimensionROM N q size) env) := by
  simp only [selectProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [prelude_eval, parentsProgram_eval counts _ children hc (by simp [Expr.cells, tDim, hk]) hk,
    descentInit_eval, descentLoop_eval labels children hl hk, finish_eval]
  simp only [Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words,
    PA17QuerySelection010b.program, PA17QuerySelection010b.core, List.append_assoc]
  rfl

theorem selectProgram_uniformLength (counts labels head children : Expr) :
    (selectProgram counts labels head children).UniformLength := by
  dsimp [selectProgram, prelude, preludeStart, preludeTail, parentsProgram, clearProgram, clearBlock,
    parentBlock, descentInit, descentLoop, descentBlock, finish, Program.sequence,
    Program.UniformLength, Program.lengthExpr, Expr.cells, tDim]
  decide
end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044e
