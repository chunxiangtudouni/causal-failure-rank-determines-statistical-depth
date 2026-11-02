module
public import PaperProofs.Structure.PA17_ProgramTemplates_041i

/-! Exact ancestor and intersection kernel templates, including both real
heap-parent loads and the original normalization pass. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041j (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041j : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041j : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def ancestorBlock (capacity parent : Expr) : Program :=
  .code [.subtract .index .address .total,
    .constant .old capacity, .add .index .old .index, .loadHeap .value .index,
    .constant .old 0, .select .fresh .value .flag .old,
    .select .flag .address .fresh .flag, .subtract .fresh .value .total,
    .select .fresh .address .fresh .value, .storeHeap .index .fresh,
    .constant .index parent, .add .index .index .address, .loadHeap .address .index]

theorem ancestorBlock_eval (capacity parent : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (ancestorBlock capacity parent).eval rom environment =
      PA17HeapAncestors001.ancestorBlock (capacity.eval rom environment) (parent.eval rom environment) := by
  simp [ancestorBlock, Program.eval, instructions, OpExpr.eval, OpExpr.subtract, OpExpr.add,
    OpExpr.loadHeap, OpExpr.select, OpExpr.storeHeap, PA17HeapAncestors001.ancestorBlock, Expr.eval]

def extensionInit (capacity stage : Expr) : Program :=
  .code [.constant .index (capacity + tDim), .loadHeap .flag .index,
    .constant .index stage, .loadHeap .address .index,
    .constant .old 0, .select .flag .address .flag .old, .constant .total 1]

theorem extensionInit_eval (capacity stage : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (extensionInit capacity stage).eval (dimensionROM N q size) environment =
      PA17HeapAncestors001.extensionInit size (capacity.eval (dimensionROM N q size) environment)
        (stage.eval (dimensionROM N q size) environment) := by
  simp [extensionInit, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.select,
    PA17HeapAncestors001.extensionInit, Expr.eval, Binary.eval, tDim, dimensionROM,
    PhysicalROM.semantic, PhysicalROM.words]

def extensionTail (capacity : Expr) : Program :=
  .code [.constant .index (capacity + tDim), .storeHeap .index .flag]

theorem extensionTail_eval (capacity : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (extensionTail capacity).eval (dimensionROM N q size) environment =
      PA17HeapAncestors001.extensionTail size (capacity.eval (dimensionROM N q size) environment) := by
  simp [extensionTail, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap,
    PA17HeapAncestors001.extensionTail, Expr.eval, Binary.eval, tDim, dimensionROM,
    PhysicalROM.semantic, PhysicalROM.words]

def extension (capacity parent stage : Expr) : Program :=
  Program.sequence [extensionInit capacity stage, .repeat 20 tDim (ancestorBlock capacity parent),
    extensionTail capacity]

theorem extension_eval (capacity parent stage : Expr) (hc : 20 ∉ capacity.cells) (hp : 20 ∉ parent.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (extension capacity parent stage).eval (dimensionROM N q size) environment =
      PA17HeapAncestors001.extensionProgram size (capacity.eval (dimensionROM N q size) environment)
        (parent.eval (dimensionROM N q size) environment) (stage.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 20 tDim (ancestorBlock capacity parent)).eval (dimensionROM N q size) environment =
      PA17HeapAncestors001.ancestorLoop (capacity.eval (dimensionROM N q size) environment)
        (parent.eval (dimensionROM N q size) environment) size := by
    change _ = (List.replicate size _).flatten
    have hrep : (List.range size).map (fun _ => PA17HeapAncestors001.ancestorBlock
        (capacity.eval (dimensionROM N q size) environment) (parent.eval (dimensionROM N q size) environment)) =
        List.replicate size (PA17HeapAncestors001.ancestorBlock
          (capacity.eval (dimensionROM N q size) environment) (parent.eval (dimensionROM N q size) environment)) := by
      simp only [List.map_const', List.length_range]
    rw [← hrep]
    change _ = (List.range size).flatMap (fun _ => PA17HeapAncestors001.ancestorBlock
      (capacity.eval (dimensionROM N q size) environment) (parent.eval (dimensionROM N q size) environment))
    apply repeat_eval_ascending 20 tDim _ _ _ size rfl
    intro index _
    rw [ancestorBlock_eval, eval_update_of_not_mem capacity _ environment 20 _ hc,
      eval_update_of_not_mem parent _ environment 20 _ hp]
  simp only [extension, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [extensionInit_eval, extensionTail_eval, hloop]
  exact List.append_assoc _ _ _ |>.symm

def minimumNode (capacity good node : Expr) : Program :=
  .code [.constant .index (capacity + node), .loadHeap .old .index,
    .constant .address (good + 1 + node), .loadHeap .fresh .address,
    .minimum .value .old .fresh, .storeHeap .index .value]

theorem minimumNode_eval (capacity good node : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (minimumNode capacity good node).eval rom environment =
      PA17UniformCell002.minimumBlock (capacity.eval rom environment) (good.eval rom environment)
        (node.eval rom environment) := by
  simp [minimumNode, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.minimum,
    OpExpr.storeHeap, PA17UniformCell002.minimumBlock, Expr.eval, Binary.eval]

def minimumPass (capacity good : Expr) : Program :=
  .repeat 20 tDim (minimumNode capacity good (tDim - .cell 20))

theorem minimumPass_eval (capacity good : Expr) (hc : 20 ∉ capacity.cells) (hg : 20 ∉ good.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (minimumPass capacity good).eval (dimensionROM N q size) environment =
      PA17UniformCell002.minimumPass size (capacity.eval (dimensionROM N q size) environment)
        (good.eval (dimensionROM N q size) environment) := by
  apply repeat_eval_ascending 20 tDim _ _ _ size rfl
  intro node hn
  rw [minimumNode_eval]
  change PA17UniformCell002.minimumBlock
    (capacity.eval (dimensionROM N q size) (Function.update environment 20 (size - node)))
    (good.eval (dimensionROM N q size) (Function.update environment 20 (size - node))) (size - (size - node)) = _
  rw [eval_update_of_not_mem capacity _ environment 20 _ hc,
    eval_update_of_not_mem good _ environment 20 _ hg, Nat.sub_sub_self hn.le]

def minimumTag (capacity good : Expr) : Program :=
  .code [.constant .index good, .loadHeap .old .index,
    .constant .index (capacity + tDim), .loadHeap .fresh .index,
    .minimum .value .old .fresh, .storeHeap .index .value]

theorem minimumTag_eval (capacity good : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (minimumTag capacity good).eval (dimensionROM N q size) environment =
      PA17UniformCell002.tagTail size (capacity.eval (dimensionROM N q size) environment)
        (good.eval (dimensionROM N q size) environment) := by
  simp [minimumTag, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.minimum,
    OpExpr.storeHeap, PA17UniformCell002.tagTail, Expr.eval, Binary.eval, tDim, dimensionROM,
    PhysicalROM.semantic, PhysicalROM.words]

def kernel (capacity good accumulator parent stage : Expr) : Program :=
  Program.sequence [extension capacity parent stage, minimumPass capacity good,
    normalize capacity accumulator, minimumTag capacity good]

theorem kernel_eval (capacity good accumulator parent stage : Expr)
    (hc : 20 ∉ capacity.cells) (hg : 20 ∉ good.cells) (ha : 20 ∉ accumulator.cells) (hp : 20 ∉ parent.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (kernel capacity good accumulator parent stage).eval (dimensionROM N q size) environment =
      PA17UniformCell002.kernelProgram size (capacity.eval (dimensionROM N q size) environment)
        (good.eval (dimensionROM N q size) environment) (accumulator.eval (dimensionROM N q size) environment)
        (parent.eval (dimensionROM N q size) environment) (stage.eval (dimensionROM N q size) environment) := by
  simp only [kernel, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [extension_eval _ _ _ hc hp, minimumPass_eval _ _ hc hg, normalize_eval _ _ hc ha, minimumTag_eval]
  simp only [PA17UniformCell002.kernelProgram, PA17UniformCell002.intersectionProgram, List.append_assoc]

theorem kernel_uniformLength (capacity good accumulator parent stage : Expr) :
    (kernel capacity good accumulator parent stage).UniformLength := by
  dsimp [kernel, extension, extensionInit, extensionTail, ancestorBlock, minimumPass,
    minimumNode, normalize, normalizeNode, clearWord, setWord, minimumTag,
    Program.sequence, Program.UniformLength, Program.lengthExpr, Expr.cells, tDim]
  decide

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
