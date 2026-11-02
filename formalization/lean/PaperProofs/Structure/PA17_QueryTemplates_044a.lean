module
public import PaperProofs.Structure.PA17_ProgramTemplates_041e
public import PaperProofs.Structure.PA17_QueryPrepare_013

/-! Fixed finite query counts/leaf-label/preparation templates. Only [N,q,t]
and lexical generator counters are read; no emitted-code ROM is an input. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041

local instance (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def countsBit (node tool : Expr) : Program :=
  .code [.constant .index (3 + nDim * qDim + node * qDim + tool), .loadROM .input .old .index,
    .constant .index (4 + nDim * qDim + tDim * qDim + tool), .loadROM .input .flag .index,
    .constant .fresh 0, .select .value .flag .old .fresh, .add .total .total .value]

theorem countsBit_eval (node tool : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (countsBit node tool).eval (dimensionROM N q size) environment =
      PA17QueryCounts008.bitBlock N q size (node.eval (dimensionROM N q size) environment)
        (tool.eval (dimensionROM N q size) environment) := by
  simp [countsBit, Program.eval, instructions, OpExpr.eval, OpExpr.loadROM, OpExpr.select, OpExpr.add,
    PA17QueryCounts008.bitBlock, Expr.eval, Binary.eval, nDim, qDim, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def countsTail (base node : Expr) : Program :=
  .code [.constant .index (base + node), .storeHeap .index .total]

theorem countsTail_eval (base node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (countsTail base node).eval (dimensionROM N q size) environment =
      PA17QueryCounts008.nodeTail (base.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  simp [countsTail, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap,
    PA17QueryCounts008.nodeTail, Expr.eval, Binary.eval]

def countsNode (base node : Expr) : Program :=
  Program.sequence [.code [.constant .total 0],
    .repeat 19 qDim (countsBit node (qDim - .cell 19)), countsTail base node]

theorem countsNode_eval (base node : Expr) (hnode : 19 ∉ node.cells) (N q size : Nat) (environment : Nat → Nat) :
    (countsNode base node).eval (dimensionROM N q size) environment =
      PA17QueryCounts008.nodeBlock N q size (base.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 19 qDim (countsBit node (qDim - .cell 19))).eval (dimensionROM N q size) environment =
      (List.range q).flatMap (PA17QueryCounts008.bitBlock N q size (node.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 19 qDim _ _ _ q rfl
    intro tool ht
    rw [countsBit_eval]
    change PA17QueryCounts008.bitBlock N q size
      (node.eval (dimensionROM N q size) (Function.update environment 19 (q - tool))) (q - (q - tool)) = _
    rw [eval_update_of_not_mem node _ environment 19 (q - tool) hnode, Nat.sub_sub_self ht.le]
  simp only [countsNode, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, countsTail_eval]
  rfl

def countsProgram (base : Expr) : Program := .repeat 18 tDim (countsNode base (tDim - .cell 18))

theorem countsProgram_eval (base : Expr) (hbase : base.cells = ∅) (N q size : Nat) (environment : Nat → Nat) :
    (countsProgram base).eval (dimensionROM N q size) environment =
      PA17QueryCounts008.program N q size (base.eval (dimensionROM N q size) environment) := by
  apply repeat_eval_ascending 18 tDim _ _ _ size rfl
  intro node hn
  rw [countsNode_eval base _ (by decide)]
  change PA17QueryCounts008.nodeBlock N q size
    (base.eval (dimensionROM N q size) (Function.update environment 18 (size - node))) (size - (size - node)) = _
  rw [eval_update_of_not_mem base _ environment 18 (size - node) (by simp [hbase]), Nat.sub_sub_self hn.le]

def labelsBit (node tool : Expr) : Program :=
  .code [.constant .index (3 + nDim * qDim + node * qDim + tool), .loadROM .input .flag .index,
    .constant .old (tool + 1), .select .value .flag .old .value, .add .total .total .flag]

theorem labelsBit_eval (node tool : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (labelsBit node tool).eval (dimensionROM N q size) environment =
      PA17LeafLabels005.bitBlock N q (node.eval (dimensionROM N q size) environment) (tool.eval (dimensionROM N q size) environment) := by
  simp [labelsBit, Program.eval, instructions, OpExpr.eval, OpExpr.loadROM, OpExpr.select, OpExpr.add,
    PA17LeafLabels005.bitBlock, Expr.eval, Binary.eval, nDim, qDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def labelsTail (base node : Expr) : Program :=
  .code [.constant .old 1, .subtract .flag .total .old, .subtract .index .old .total, .add .flag .flag .index,
    .constant .old 0, .select .value .flag .old .value, .constant .index (base + node), .storeHeap .index .value]

theorem labelsTail_eval (base node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (labelsTail base node).eval (dimensionROM N q size) environment =
      PA17LeafLabels005.nodeTail (base.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  simp [labelsTail, Program.eval, instructions, OpExpr.eval, OpExpr.subtract, OpExpr.add, OpExpr.select, OpExpr.storeHeap,
    PA17LeafLabels005.nodeTail, Expr.eval, Binary.eval]

def labelsNode (base node : Expr) : Program :=
  Program.sequence [.code [.constant .total 0, .constant .value 0],
    .repeat 19 qDim (labelsBit node (qDim - .cell 19)), labelsTail base node]

theorem labelsNode_eval (base node : Expr) (hnode : 19 ∉ node.cells) (N q size : Nat) (environment : Nat → Nat) :
    (labelsNode base node).eval (dimensionROM N q size) environment =
      PA17LeafLabels005.nodeBlock N q (base.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 19 qDim (labelsBit node (qDim - .cell 19))).eval (dimensionROM N q size) environment =
      (List.range q).flatMap (PA17LeafLabels005.bitBlock N q (node.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 19 qDim _ _ _ q rfl
    intro tool ht
    rw [labelsBit_eval]
    change PA17LeafLabels005.bitBlock N q
      (node.eval (dimensionROM N q size) (Function.update environment 19 (q - tool))) (q - (q - tool)) = _
    rw [eval_update_of_not_mem node _ environment 19 (q - tool) hnode, Nat.sub_sub_self ht.le]
  simp only [labelsNode, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, labelsTail_eval]
  rfl

def labelsProgram (base : Expr) : Program := .repeat 18 tDim (labelsNode base (tDim - .cell 18))

theorem labelsProgram_eval (base : Expr) (hbase : base.cells = ∅) (N q size : Nat) (environment : Nat → Nat) :
    (labelsProgram base).eval (dimensionROM N q size) environment =
      PA17LeafLabels005.program N q size (base.eval (dimensionROM N q size) environment) := by
  apply repeat_eval_ascending 18 tDim _ _ _ size rfl
  intro node hn
  rw [labelsNode_eval base _ (by decide)]
  change PA17LeafLabels005.nodeBlock N q
    (base.eval (dimensionROM N q size) (Function.update environment 18 (size - node))) (size - (size - node)) = _
  rw [eval_update_of_not_mem base _ environment 18 (size - node) (by simp [hbase]), Nat.sub_sub_self hn.le]

def prepareProgram (metadata labels counts : Expr) : Program :=
  Program.sequence [metadataProgram metadata, labelsProgram labels, countsProgram counts]

theorem prepareProgram_eval (metadata labels counts : Expr) (hm : metadata.cells = ∅) (hl : labels.cells = ∅) (hc : counts.cells = ∅)
    (N q size : Nat) (environment : Nat → Nat) :
    (prepareProgram metadata labels counts).eval (dimensionROM N q size) environment =
      PA17QueryPrepare013.program N q size (metadata.eval (dimensionROM N q size) environment)
        (labels.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment) := by
  simp only [prepareProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [metadataProgram_eval metadata hm, labelsProgram_eval labels hl, countsProgram_eval counts hc]
  simp only [PA17QueryPrepare013.program, PA17QueryMetadata010.program, List.append_assoc]

theorem countsProgram_uniformLength (base : Expr) : (countsProgram base).UniformLength := by
  dsimp [Program.UniformLength, countsProgram, countsNode, countsBit, countsTail, Program.sequence,
    Program.lengthExpr, Expr.cells, qDim, tDim]
  decide

theorem labelsProgram_uniformLength (base : Expr) : (labelsProgram base).UniformLength := by
  dsimp [Program.UniformLength, labelsProgram, labelsNode, labelsBit, labelsTail, Program.sequence,
    Program.lengthExpr, Expr.cells, qDim, tDim]
  decide

theorem prepareProgram_uniformLength (metadata labels counts : Expr) : (prepareProgram metadata labels counts).UniformLength := by
  simp only [prepareProgram, Program.sequence, Program.UniformLength]
  exact ⟨metadataProgram_uniformLength metadata, labelsProgram_uniformLength labels, countsProgram_uniformLength counts, True.intro⟩

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044a
