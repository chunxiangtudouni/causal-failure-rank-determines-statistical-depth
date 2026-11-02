module

public import Structure.PSTR_BuildLower_ConcreteHeap_028

/-! Existing ISA register/heap actions do not read PC/halted. This pure
instruction-data congruence lifts an existing standalone access certificate
to the SAME real straight-prefix data, without equating fetched runs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.WordDataCongr
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

theorem operation (physical : PhysicalROM) (op : PackingOp) (before after : WordState bits)
    (registers : before.register = after.register) (heaps : before.heap = after.heap) :
    (packingExecuteOp physical op before).register = (packingExecuteOp physical op after).register ∧
      (packingExecuteOp physical op before).heap = (packingExecuteOp physical op after).heap := by
  cases op with
  | base source =>
    cases source with
    | base instruction =>
      cases instruction <;> simp [packingExecuteOp, wordOp, wordInstruction, registers, heaps]
    | subtract target left right => simp [packingExecuteOp, wordOp, registers, heaps]
  | arithmetic binary target left right => simp [packingExecuteOp, registers, heaps]
  | jumpIfZero condition target => exact ⟨registers, heaps⟩

theorem operations (physical : PhysicalROM) (code : List PackingOp) (before after : WordState bits)
    (registers : before.register = after.register) (heaps : before.heap = after.heap) :
    (executeOps physical code before).register = (executeOps physical code after).register ∧
      (executeOps physical code before).heap = (executeOps physical code after).heap := by
  induction code generalizing before after with
  | nil => exact ⟨registers, heaps⟩
  | cons op later ih =>
    have step := operation physical op before after registers heaps
    exact ih _ _ step.1 step.2

theorem access (physical : PhysicalROM) (heapWords : Nat) (op : PackingOp) (before after : WordState bits)
    (registers : before.register = after.register) :
    packingAccessFits physical heapWords before op = packingAccessFits physical heapWords after op := by
  cases op with
  | base source =>
    cases source with
    | base instruction => cases instruction <;> simp [packingAccessFits, AccessFits, registers]
    | subtract target left right => rfl
  | arithmetic binary target left right => rfl
  | jumpIfZero condition target => rfl

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.WordDataCongr
