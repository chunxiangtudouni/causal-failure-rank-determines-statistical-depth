module
public import PaperProofs.Structure.PA17_QueryTemplates_044c
public import PaperProofs.Structure.PA17_QueryRanks_011

/-! Fixed dimension-only rank scans and reply instructions for actual Query019. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044d
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041
local instance pa17OfNat044d (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add044d : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub044d : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def flagBlock (flags budget : Expr) : Program := .code [
  .constant .index (flags + budget), .loadHeap .flag .index,
  .constant .old budget, .select .value .flag .value .old]

theorem flagBlock_eval (flags budget : Expr) (rom : PhysicalROM) (env : Nat → Nat) :
    (flagBlock flags budget).eval rom env = PA17QueryRanks011.flagBlock (flags.eval rom env) (budget.eval rom env) := by
  simp [flagBlock, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.select,
    PA17QueryRanks011.flagBlock, Expr.eval, Binary.eval]

def rankProgram (flags output : Expr) : Program := Program.sequence [
  .code [.constant .value (qDim + 2)], .repeat 17 (qDim + 2) (flagBlock flags (.cell 17 - 1)),
  .code [.constant .index output, .storeHeap .index .value]]

theorem rankProgram_eval (flags output : Expr) (hf : flags.cells = ∅) (N q size : Nat) (env : Nat → Nat) :
    (rankProgram flags output).eval (dimensionROM N q size) env =
      PA17QueryRanks011.rankProgram q (flags.eval (dimensionROM N q size) env) (output.eval (dimensionROM N q size) env) := by
  have hh : (Program.repeat 17 (qDim + 2) (flagBlock flags (.cell 17 - 1))).eval (dimensionROM N q size) env =
      (List.range (q + 2)).reverse.flatMap (PA17QueryRanks011.flagBlock (flags.eval (dimensionROM N q size) env)) := by
    apply repeat_eval_descending 17 (qDim + 2) _ _ _ (q + 2) rfl
    intro budget _
    rw [flagBlock_eval]
    change PA17QueryRanks011.flagBlock (flags.eval _ (Function.update env 17 (budget + 1))) (budget + 1 - 1) = _
    rw [eval_update_of_not_mem flags _ env 17 _ (by simp [hf]), Nat.add_sub_cancel]
  simp only [rankProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hh]
  simp [Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap, Expr.eval, Binary.eval, qDim,
    dimensionROM, PhysicalROM.semantic, PhysicalROM.words, PA17QueryRanks011.rankProgram,
    PA17QueryRanks011.scan, List.range_eq_range']

def rankFinish (head : Expr) : Program := .code [
  .constant .address (head + 2), .loadHeap .index .address,
  .constant .address (head + 4), .loadHeap .old .address,
  .constant .address (head + 5), .loadHeap .fresh .address,
  .constant .total 1, .add .value .fresh .total, .minimum .value .old .value,
  .subtract .total .fresh .total, .constant .address (head + 6), .storeHeap .address .total,
  .constant .total 0, .constant .flag 1, .select .flag .fresh .flag .total,
  .select .flag .index .flag .total, .constant .address (head + 7), .storeHeap .address .flag,
  .constant .flag (qDim + 2), .select .old .index .old .flag,
  .select .fresh .index .fresh .total, .select .value .index .value .flag, .constant .index 0]

theorem rankFinish_eval (head : Expr) (N q size : Nat) (env : Nat → Nat) :
    (rankFinish head).eval (dimensionROM N q size) env = PA17QueryRanks011.finish q (head.eval (dimensionROM N q size) env) := by
  simp [rankFinish, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.storeHeap,
    OpExpr.add, OpExpr.minimum, OpExpr.subtract, OpExpr.select, Expr.eval, Binary.eval, qDim,
    dimensionROM, PhysicalROM.semantic, PhysicalROM.words, PA17QueryRanks011.finish]

def ranksProgram (good bad head : Expr) : Program :=
  Program.sequence [rankProgram good (head + 4), rankProgram bad (head + 5), rankFinish head]

theorem ranksProgram_eval (good bad head : Expr) (hg : good.cells = ∅) (hb : bad.cells = ∅)
    (N q size : Nat) (env : Nat → Nat) :
    (ranksProgram good bad head).eval (dimensionROM N q size) env = PA17QueryRanks011.program q
      (good.eval (dimensionROM N q size) env) (bad.eval (dimensionROM N q size) env) (head.eval (dimensionROM N q size) env) := by
  simp only [ranksProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rankProgram_eval good _ hg, rankProgram_eval bad _ hb, rankFinish_eval]
  simp only [Expr.eval, Binary.eval, PA17QueryRanks011.program, List.append_assoc]

def replyProgram (head tool : Expr) : Program := .code [
  .constant .address tool, .loadHeap .index .address,
  .constant .address (head + 2), .loadHeap .flag .address,
  .constant .address (head + 4), .loadHeap .old .address,
  .constant .address (head + 5), .loadHeap .fresh .address,
  .constant .total 1, .add .value .fresh .total, .minimum .value .old .value,
  .constant .total (qDim + 2), .select .old .flag .old .total,
  .select .value .flag .value .total, .constant .total 0,
  .select .fresh .flag .fresh .total, .select .index .flag .index .total]

theorem replyProgram_eval (head tool : Expr) (N q size : Nat) (env : Nat → Nat) :
    (replyProgram head tool).eval (dimensionROM N q size) env = PA17QueryRanks011.replyProgram q
      (head.eval (dimensionROM N q size) env) (tool.eval (dimensionROM N q size) env) := by
  simp [replyProgram, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.add, OpExpr.minimum,
    OpExpr.select, Expr.eval, Binary.eval, qDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words,
    PA17QueryRanks011.replyProgram]

theorem rankProgram_uniformLength (flags output : Expr) : (rankProgram flags output).UniformLength := by
  dsimp [rankProgram, flagBlock, Program.sequence, Program.UniformLength, Program.lengthExpr, Expr.cells, qDim]
  decide

theorem ranksProgram_uniformLength (good bad head : Expr) : (ranksProgram good bad head).UniformLength := by
  dsimp [ranksProgram, rankProgram, flagBlock, rankFinish, Program.sequence,
    Program.UniformLength, Program.lengthExpr, Expr.cells, qDim]
  decide

theorem replyProgram_uniformLength (head tool : Expr) : (replyProgram head tool).UniformLength := trivial
end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044d
