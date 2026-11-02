module
public import PaperProofs.Structure.PA17_ProgramTemplates_041e
public import PaperProofs.Structure.PA17_StageMap_001

/-! Exact raw stage/node incidence-code templates. No stage lookup result or
input data is part of the generated instruction stream. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041g (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041g : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041g : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul041g : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def stageBit (stage node tool : Expr) : Program :=
  .code [.constant .index (3 + stage * qDim + tool), .loadROM .input .old .index,
    .constant .index (3 + nDim * qDim + node * qDim + tool), .loadROM .input .fresh .index,
    .subtract .flag .old .fresh, .subtract .index .fresh .old,
    .add .flag .flag .index, .add .total .total .flag]

theorem stageBit_eval (stage node tool : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (stageBit stage node tool).eval (dimensionROM N q size) environment =
      PA17StageMap001.bitBlock N q (stage.eval (dimensionROM N q size) environment)
        (node.eval (dimensionROM N q size) environment) (tool.eval (dimensionROM N q size) environment) := by
  simp [stageBit, Program.eval, instructions, OpExpr.eval, OpExpr.loadROM, OpExpr.subtract, OpExpr.add,
    PA17StageMap001.bitBlock, Expr.eval, Binary.eval, nDim, qDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def stageNodeTail (node : Expr) : Program :=
  .code [.constant .old (node + 1), .select .value .total .value .old]

theorem stageNodeTail_eval (node : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (stageNodeTail node).eval rom environment = PA17StageMap001.nodeTail (node.eval rom environment) := by
  simp [stageNodeTail, Program.eval, instructions, OpExpr.eval, OpExpr.select,
    PA17StageMap001.nodeTail, Expr.eval, Binary.eval]

def stageNode (stage node : Expr) : Program :=
  Program.sequence [.code [.constant .total 0],
    .repeat 19 qDim (stageBit stage node (qDim - .cell 19)), stageNodeTail node]

theorem stageNode_eval (stage node : Expr) (hs : 19 ∉ stage.cells) (hn : 19 ∉ node.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (stageNode stage node).eval (dimensionROM N q size) environment =
      PA17StageMap001.nodeBlock N q (stage.eval (dimensionROM N q size) environment)
        (node.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 19 qDim (stageBit stage node (qDim - .cell 19))).eval
      (dimensionROM N q size) environment = (List.range q).flatMap
      (PA17StageMap001.bitBlock N q (stage.eval (dimensionROM N q size) environment)
        (node.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 19 qDim _ _ _ q rfl
    intro tool ht
    rw [stageBit_eval]
    change PA17StageMap001.bitBlock N q
      (stage.eval (dimensionROM N q size) (Function.update environment 19 (q - tool)))
      (node.eval (dimensionROM N q size) (Function.update environment 19 (q - tool))) (q - (q - tool)) = _
    rw [eval_update_of_not_mem stage _ environment 19 _ hs, eval_update_of_not_mem node _ environment 19 _ hn,
      Nat.sub_sub_self ht.le]
  simp only [stageNode, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, stageNodeTail_eval]
  rfl

def stageSave (base stage : Expr) : Program :=
  .code [.constant .index (base + stage), .storeHeap .index .value]

theorem stageSave_eval (base stage : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (stageSave base stage).eval rom environment =
      PA17StageMap001.stageTail (base.eval rom environment) (stage.eval rom environment) := by
  simp [stageSave, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap,
    PA17StageMap001.stageTail, Expr.eval, Binary.eval]

def stageBlock (base stage : Expr) : Program :=
  Program.sequence [.code [.constant .value 0], .repeat 18 tDim (stageNode stage (tDim - .cell 18)),
    stageSave base stage]

theorem stageBlock_eval (base stage : Expr) (h18 : 18 ∉ stage.cells) (h19 : 19 ∉ stage.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (stageBlock base stage).eval (dimensionROM N q size) environment =
      PA17StageMap001.stageBlock N q size (base.eval (dimensionROM N q size) environment)
        (stage.eval (dimensionROM N q size) environment) := by
  have hloop : (Program.repeat 18 tDim (stageNode stage (tDim - .cell 18))).eval
      (dimensionROM N q size) environment = (List.range size).flatMap
      (PA17StageMap001.nodeBlock N q (stage.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 18 tDim _ _ _ size rfl
    intro node hn
    rw [stageNode_eval stage _ h19 (by decide)]
    change PA17StageMap001.nodeBlock N q
      (stage.eval (dimensionROM N q size) (Function.update environment 18 (size - node))) (size - (size - node)) = _
    rw [eval_update_of_not_mem stage _ environment 18 _ h18, Nat.sub_sub_self hn.le]
  simp only [stageBlock, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop, stageSave_eval]
  rfl

def stageProgram (base : Expr) : Program :=
  .repeat 16 nDim (stageBlock base (nDim - .cell 16))

theorem stageProgram_eval (base : Expr) (hbase : base.cells = ∅) (N q size : Nat) (environment : Nat → Nat) :
    (stageProgram base).eval (dimensionROM N q size) environment =
      PA17StageMap001.program N q size (base.eval (dimensionROM N q size) environment) := by
  apply repeat_eval_ascending 16 nDim _ _ _ N rfl
  intro stage hs
  rw [stageBlock_eval base _ (by decide) (by decide)]
  change PA17StageMap001.stageBlock N q size
    (base.eval (dimensionROM N q size) (Function.update environment 16 (N - stage))) (N - (N - stage)) = _
  rw [eval_update_of_not_mem base _ environment 16 _ (by simp [hbase]), Nat.sub_sub_self hs.le]

theorem stageProgram_uniformLength (base : Expr) : (stageProgram base).UniformLength := by
  dsimp [stageProgram, stageBlock, stageNode, stageNodeTail, stageBit, stageSave,
    Program.UniformLength, Program.lengthExpr, Program.sequence, Expr.cells, nDim, qDim, tDim]
  decide

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
