module
public import PaperProofs.Structure.PA17_ProgramTemplates_041c
public import PaperProofs.Structure.PA17_QueryMetadata_010
public import PaperProofs.Structure.PA17_CellLayout_003

/-! Fixed metadata-code template. Dimensions are read only from [N,q,t];
the exact original metadata instructions and both actual loops are emitted. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d

local instance (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def nDim : Expr := .input 0
def qDim : Expr := .input 1
def tDim : Expr := .input 2

def dimensionROM (N q size : Nat) : PhysicalROM := ⟨[N, q, size], [], []⟩

theorem eval_update_of_not_mem (expression : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (counter value : Nat) (hcounter : counter ∉ expression.cells) :
    expression.eval rom (Function.update environment counter value) = expression.eval rom environment := by
  apply Expr.eval_cells_congr expression rom expression.cells (fun _ ha => ha) environment _
  intro address ha
  exact Function.update_of_ne (by intro he; subst address; exact hcounter ha) _ _

def metadataBit (node tool : Expr) : Program :=
  .code [.constant .index (3 + nDim * qDim + node * qDim + tool),
    .loadROM .input .value .index, .add .total .total .value]

theorem metadataBit_eval (node tool : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (metadataBit node tool).eval (dimensionROM N q size) environment =
      UniformTreeMetadataRAM.readBit N q (node.eval (dimensionROM N q size) environment)
        (tool.eval (dimensionROM N q size) environment) := by
  simp [metadataBit, Program.eval, instructions, OpExpr.eval, OpExpr.loadROM, OpExpr.add,
    UniformTreeMetadataRAM.readBit, Expr.eval, Binary.eval, nDim, qDim, dimensionROM,
    PhysicalROM.semantic, PhysicalROM.words]

def metadataTail (base node : Expr) : Program :=
  .code [.constant .index (base + node), .storeHeap .index .total,
    .constant .index node, .loadROM .internal .value .index,
    .constant .index (base + tDim + (node + 1)), .storeHeap .index .value,
    .constant .index (tDim + node), .loadROM .internal .flag .index,
    .constant .old 0, .constant .fresh 1, .select .value .flag .fresh .old,
    .constant .index (base + 2 * tDim + 1 + node), .storeHeap .index .value]

theorem metadataTail_eval (base node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (metadataTail base node).eval (dimensionROM N q size) environment =
      UniformTreeMetadataRAM.nodeTail size (base.eval (dimensionROM N q size) environment)
        (node.eval (dimensionROM N q size) environment) := by
  simp [metadataTail, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap, OpExpr.loadROM,
    OpExpr.select, UniformTreeMetadataRAM.nodeTail, UniformTreeMetadataRAM.cardAddress,
    UniformTreeMetadataRAM.parentAddress, UniformTreeMetadataRAM.internalAddress,
    Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def metadataNode (base node : Expr) : Program :=
  Program.sequence [.code [.constant .total 0],
    .repeat 19 qDim (metadataBit node (qDim - .cell 19)), metadataTail base node]

theorem metadataNode_eval (base node : Expr) (hnode : 19 ∉ node.cells) (N q size : Nat)
    (environment : Nat → Nat) :
    (metadataNode base node).eval (dimensionROM N q size) environment =
      UniformTreeMetadataRAM.nodeBlock N q size (base.eval (dimensionROM N q size) environment)
        (node.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 19 qDim (metadataBit node (qDim - .cell 19))).eval
      (dimensionROM N q size) environment =
      (List.range q).flatMap (UniformTreeMetadataRAM.readBit N q (node.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 19 qDim _ _ _ q rfl
    intro tool ht
    rw [metadataBit_eval]
    change UniformTreeMetadataRAM.readBit N q
      (node.eval (dimensionROM N q size) (Function.update environment 19 (q - tool))) (q - (q - tool)) = _
    rw [eval_update_of_not_mem node _ environment 19 (q - tool) hnode, Nat.sub_sub_self ht.le]
  simp only [metadataNode, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, metadataTail_eval]
  rfl

def metadataClear (base : Expr) : Program :=
  .code [.constant .index (base + tDim), .constant .value 0, .storeHeap .index .value]

theorem metadataClear_eval (base : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (metadataClear base).eval (dimensionROM N q size) environment =
      UniformNormalizationRAM.clearBlock (UniformTreeMetadataRAM.parentAddress size
        (base.eval (dimensionROM N q size) environment) 0) := by
  simp [metadataClear, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap,
    UniformNormalizationRAM.clearBlock, UniformTreeMetadataRAM.parentAddress,
    Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def metadataProgram (base : Expr) : Program :=
  .append (metadataClear base) (.repeat 18 tDim (metadataNode base (tDim - .cell 18)))

theorem metadataProgram_eval (base : Expr) (hbase : base.cells = ∅) (N q size : Nat)
    (environment : Nat → Nat) :
    (metadataProgram base).eval (dimensionROM N q size) environment =
      UniformTreeMetadataRAM.program N q size (base.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 18 tDim (metadataNode base (tDim - .cell 18))).eval
      (dimensionROM N q size) environment =
      (List.range size).flatMap (UniformTreeMetadataRAM.nodeBlock N q size
        (base.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 18 tDim _ _ _ size rfl
    intro node hn
    rw [metadataNode_eval base _ (by decide)]
    change UniformTreeMetadataRAM.nodeBlock N q size
      (base.eval (dimensionROM N q size) (Function.update environment 18 (size - node)))
      (size - (size - node)) = _
    rw [eval_update_of_not_mem base _ environment 18 (size - node) (by simp [hbase]), Nat.sub_sub_self hn.le]
  rw [metadataProgram, Program.eval, metadataClear_eval, hloop]
  rfl

def fullCapacity : Expr := (nDim + 1) * (qDim + 2) * (tDim + 1) + 2 * (tDim + 1)

theorem fullCapacity_cells : fullCapacity.cells = ∅ := by simp [fullCapacity, Expr.cells, nDim, qDim, tDim]

theorem fullCapacity_eval (N q size : Nat) (environment : Nat → Nat) :
    fullCapacity.eval (dimensionROM N q size) environment = PA17CellLayout003.capacityWords N q size := by
  rfl

theorem fullMetadata_template (N q size : Nat) (environment : Nat → Nat) :
    (metadataProgram fullCapacity).haltingTemplate.denote (dimensionROM N q size) environment =
      haltingWords (UniformTreeMetadataRAM.program N q size (PA17CellLayout003.capacityWords N q size)) := by
  rw [Program.haltingTemplate_denote, metadataProgram_eval fullCapacity fullCapacity_cells, fullCapacity_eval]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
