module
public import PaperProofs.Structure.PA17_QueryTemplates_044b
public import PaperProofs.Structure.PA17_QueryTests_009

/-! Exact finite templates for the real dynamic budget tests, with the
original ascending budget/node scans and fixed-fuel parent iterations. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041

local instance (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance : HMul Expr Expr Expr := ⟨.binary .multiply⟩

theorem repeat_eval_block (counter : Nat) (bound : Expr) (body : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (count : Nat) (block : List Op) (hb : bound.eval rom environment = count)
    (hs : ∀ index < count, body.eval rom (Function.update environment counter (index + 1)) = block) :
    (Program.repeat counter bound body).eval rom environment = (List.replicate count block).flatten := by
  rw [Program.eval, hb]
  have hh : (List.range count).reverse.flatMap (fun index => body.eval rom (Function.update environment counter (index + 1))) =
      (List.range count).reverse.flatMap (fun _ => block) := by
    apply List.flatMap_congr
    intro index hi
    exact hs index (List.mem_range.mp (List.mem_reverse.mp hi))
  rw [hh]
  simp only [List.flatMap, List.map_const', List.length_reverse, List.length_range]

theorem finRange_values (count : Nat) : (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem
  · simp
  · intro index hi hj
    simp

theorem finRange_flatMap (count : Nat) (block : Nat → List Op) :
    (List.finRange count).flatMap (fun index => block index.val) = (List.range count).flatMap block := by
  have hh := congrArg (fun indices : List Nat => indices.flatMap block) (finRange_values count)
  simpa only [List.flatMap_map] using hh

def acceptInit (row budget : Expr) : Program := .code [
  .constant .index row, .loadHeap .address .index, .constant .index (budget * (tDim + 1)), .add .address .address .index,
  .loadHeap .value .address, .constant .fresh 0, .constant .flag 1, .select .flag .value .flag .fresh]

theorem acceptInit_eval (row budget : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (acceptInit row budget).eval (dimensionROM N q size) environment = PA17QueryTests009.acceptInit size
      (row.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment) := by
  simp [acceptInit, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.add, OpExpr.select,
    PA17QueryTests009.acceptInit, Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def acceptNode (row counts budget node : Expr) : Program := .code [
  .constant .index row, .loadHeap .address .index, .constant .index (budget * (tDim + 1) + 1 + node), .add .address .address .index,
  .loadHeap .value .address, .constant .index (counts + node), .loadHeap .total .index, .subtract .old .total .value,
  .constant .fresh 0, .select .flag .old .fresh .flag]

theorem acceptNode_eval (row counts budget node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (acceptNode row counts budget node).eval (dimensionROM N q size) environment = PA17QueryTests009.acceptNode size
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment)
      (budget.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment) := by
  simp [acceptNode, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.add, OpExpr.subtract, OpExpr.select,
    PA17QueryTests009.acceptNode, Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def acceptProgram (row counts budget : Expr) : Program := .append (acceptInit row budget)
  (.repeat 18 tDim (acceptNode row counts budget (tDim - .cell 18)))

theorem acceptProgram_eval (row counts budget : Expr) (hr : row.cells = ∅) (hc : counts.cells = ∅) (hb : 18 ∉ budget.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (acceptProgram row counts budget).eval (dimensionROM N q size) environment = PA17QueryTests009.acceptProgram size
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment) := by
  have hl : (Program.repeat 18 tDim (acceptNode row counts budget (tDim - .cell 18))).eval (dimensionROM N q size) environment =
      (List.range size).flatMap (PA17QueryTests009.acceptNode size (row.eval (dimensionROM N q size) environment)
        (counts.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment)) := by
    apply repeat_eval_ascending 18 tDim _ _ _ size rfl
    intro node hn
    rw [acceptNode_eval]
    change PA17QueryTests009.acceptNode size (row.eval _ (Function.update environment 18 (size - node)))
      (counts.eval _ (Function.update environment 18 (size - node))) (budget.eval _ (Function.update environment 18 (size - node))) (size - (size - node)) = _
    rw [eval_update_of_not_mem row _ environment 18 (size - node) (by simp [hr]),
      eval_update_of_not_mem counts _ environment 18 (size - node) (by simp [hc]),
      eval_update_of_not_mem budget _ environment 18 (size - node) hb, Nat.sub_sub_self hn.le]
  rw [acceptProgram, Program.eval, acceptInit_eval, hl]
  rfl

def storeFlag (target : Expr) : Program := .code [.constant .index target, .storeHeap .index .flag]
def badInit (node : Expr) : Program := .code [.constant .index node, .loadHeap .address .index,
  .constant .old 0, .select .flag .address .flag .old, .constant .total 1]

theorem storeFlag_eval (target : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (storeFlag target).eval (dimensionROM N q size) environment = PA17QueryTests009.storeFlag (target.eval (dimensionROM N q size) environment) := by
  simp [storeFlag, Program.eval, instructions, OpExpr.eval, OpExpr.storeHeap, PA17QueryTests009.storeFlag]

theorem badInit_eval (node : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (badInit node).eval (dimensionROM N q size) environment = PA17QueryTests009.badInit (node.eval (dimensionROM N q size) environment) := by
  simp [badInit, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.select, PA17QueryTests009.badInit, Expr.eval]

def badNode (row counts parents budget : Expr) : Program := .code [
  .subtract .index .address .total, .constant .old row, .loadHeap .old .old,
  .constant .value (budget * (tDim + 1) + 1), .add .old .old .value, .add .index .old .index,
  .loadHeap .value .index, .subtract .index .address .total, .constant .old counts, .add .index .old .index,
  .loadHeap .fresh .index, .subtract .value .value .fresh, .constant .old 0, .select .fresh .value .flag .old,
  .select .flag .address .fresh .flag, .constant .index parents, .add .index .index .address, .loadHeap .address .index]

theorem badNode_eval (row counts parents budget : Expr) (N q size : Nat) (environment : Nat → Nat) :
    (badNode row counts parents budget).eval (dimensionROM N q size) environment = PA17QueryTests009.badNode size
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment)
      (parents.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment) := by
  simp [badNode, Program.eval, instructions, OpExpr.eval, OpExpr.loadHeap, OpExpr.add, OpExpr.subtract, OpExpr.select,
    PA17QueryTests009.badNode, Expr.eval, Binary.eval, tDim, dimensionROM, PhysicalROM.semantic, PhysicalROM.words]

def badLoop (row counts parents budget : Expr) : Program := .repeat 20 tDim (badNode row counts parents budget)

theorem badLoop_eval (row counts parents budget : Expr) (hr : row.cells = ∅) (hc : counts.cells = ∅) (hp : parents.cells = ∅)
    (hb : 20 ∉ budget.cells) (N q size : Nat) (environment : Nat → Nat) :
    (badLoop row counts parents budget).eval (dimensionROM N q size) environment = PA17QueryTests009.badLoop size
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment)
      (parents.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment) size := by
  apply repeat_eval_block 20 tDim _ _ _ size _ rfl
  intro index hi
  rw [badNode_eval, eval_update_of_not_mem row _ environment 20 (index + 1) (by simp [hr]),
    eval_update_of_not_mem counts _ environment 20 (index + 1) (by simp [hc]),
    eval_update_of_not_mem parents _ environment 20 (index + 1) (by simp [hp]),
    eval_update_of_not_mem budget _ environment 20 (index + 1) hb]

def budgetProgram (row counts parents node good bad budget : Expr) : Program := Program.sequence [
  acceptProgram row counts budget, storeFlag (good + budget), .append (badInit node) (badLoop row counts parents budget), storeFlag (bad + budget)]

theorem budgetProgram_eval (row counts parents node good bad budget : Expr)
    (hr : row.cells = ∅) (hc : counts.cells = ∅) (hp : parents.cells = ∅) (h18 : 18 ∉ budget.cells) (h20 : 20 ∉ budget.cells)
    (N q size : Nat) (environment : Nat → Nat) :
    (budgetProgram row counts parents node good bad budget).eval (dimensionROM N q size) environment = PA17QueryTests009.budgetProgram size
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment)
      (parents.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment)
      (good.eval (dimensionROM N q size) environment) (bad.eval (dimensionROM N q size) environment) (budget.eval (dimensionROM N q size) environment) := by
  simp only [budgetProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil, Program.eval]
  rw [acceptProgram_eval row counts budget hr hc h18, storeFlag_eval, badInit_eval,
    badLoop_eval row counts parents budget hr hc hp h20, storeFlag_eval]
  simp only [Expr.eval, Binary.eval, PA17QueryTests009.budgetProgram, PA17QueryTests009.badProgram, List.append_assoc]

def testsProgram (row counts parents node good bad : Expr) : Program :=
  .repeat 17 (qDim + 2) (budgetProgram row counts parents node good bad (qDim + 2 - .cell 17))

theorem testsProgram_eval (row counts parents node good bad : Expr)
    (hr : row.cells = ∅) (hc : counts.cells = ∅) (hp : parents.cells = ∅) (hn : node.cells = ∅) (hg : good.cells = ∅) (hb : bad.cells = ∅)
    (N q size : Nat) (environment : Nat → Nat) :
    (testsProgram row counts parents node good bad).eval (dimensionROM N q size) environment = PA17QueryTests009.program size q
      (row.eval (dimensionROM N q size) environment) (counts.eval (dimensionROM N q size) environment)
      (parents.eval (dimensionROM N q size) environment) (node.eval (dimensionROM N q size) environment)
      (good.eval (dimensionROM N q size) environment) (bad.eval (dimensionROM N q size) environment) := by
  rw [PA17QueryTests009.program, finRange_flatMap]
  apply repeat_eval_ascending 17 (qDim + 2) _ _ _ (q + 2) rfl
  intro budget hbudget
  rw [budgetProgram_eval row counts parents node good bad _ hr hc hp (by decide) (by decide)]
  change PA17QueryTests009.budgetProgram size
    (row.eval _ (Function.update environment 17 (q + 2 - budget))) (counts.eval _ (Function.update environment 17 (q + 2 - budget)))
    (parents.eval _ (Function.update environment 17 (q + 2 - budget))) (node.eval _ (Function.update environment 17 (q + 2 - budget)))
    (good.eval _ (Function.update environment 17 (q + 2 - budget))) (bad.eval _ (Function.update environment 17 (q + 2 - budget)))
    (q + 2 - (q + 2 - budget)) = _
  rw [eval_update_of_not_mem row _ environment 17 _ (by simp [hr]), eval_update_of_not_mem counts _ environment 17 _ (by simp [hc]),
    eval_update_of_not_mem parents _ environment 17 _ (by simp [hp]), eval_update_of_not_mem node _ environment 17 _ (by simp [hn]),
    eval_update_of_not_mem good _ environment 17 _ (by simp [hg]), eval_update_of_not_mem bad _ environment 17 _ (by simp [hb]),
    Nat.sub_sub_self hbudget.le]

theorem testsProgram_uniformLength (row counts parents node good bad : Expr) : (testsProgram row counts parents node good bad).UniformLength := by
  dsimp [testsProgram, budgetProgram, acceptProgram, acceptInit, acceptNode, storeFlag, badInit, badLoop, badNode,
    Program.sequence, Program.UniformLength, Program.lengthExpr, Expr.cells, qDim, tDim]
  decide

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044c
