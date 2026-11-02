module

public import Structure.PSTR_BuildLower_FixedExpr_010

/-! Literal ALU operations inline fixed relative-bank loads and stores. Runtime
controlBase is carried by .address, not embedded as a code immediate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

def registerOffset (reg : Register) : Nat := 32 + reg.word

def portRegisters (base : BitVec bits) (heap : BitVec bits → BitVec bits)
    (reg : Register) : BitVec bits := heap (base + BitVec.ofNat bits (registerOffset reg))

def ValueOp.relativeLower : ValueOp → List PackingOp
  | .constant target value =>
      [.base (.base (.constant .value value))] ++ relativeWrite (registerOffset target)
  | .add target left right =>
      relativeRead (registerOffset left) .old ++ relativeRead (registerOffset right) .fresh ++
        [.base (.base (.add .value .old .fresh))] ++ relativeWrite (registerOffset target)
  | .minimum target left right =>
      relativeRead (registerOffset left) .old ++ relativeRead (registerOffset right) .fresh ++
        [.base (.base (.minimum .value .old .fresh))] ++ relativeWrite (registerOffset target)
  | .select target condition whenTrue whenFalse =>
      relativeRead (registerOffset condition) .flag ++ relativeRead (registerOffset whenTrue) .old ++
        relativeRead (registerOffset whenFalse) .fresh ++
        [.base (.base (.select .value .flag .old .fresh))] ++ relativeWrite (registerOffset target)
  | .subtract target left right =>
      relativeRead (registerOffset left) .old ++ relativeRead (registerOffset right) .fresh ++
        [.base (.subtract .value .old .fresh)] ++ relativeWrite (registerOffset target)

theorem relativeValue_length (op : ValueOp) : op.relativeLower.length ≤ 13 := by
  cases op <;> simp [ValueOp.relativeLower, relativeRead_length, relativeWrite_length]

theorem relativeValue_straight (op : ValueOp) : StraightProgram op.relativeLower := by
  cases op <;>
    simp [ValueOp.relativeLower, relativeRead, relativeWrite, StraightProgram, StraightOp]

theorem relativeValue_heap (op : ValueOp) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom op.relativeLower state).heap =
      Function.update state.heap
        (state.register .address + BitVec.ofNat bits (registerOffset op.target))
        (op.value (portRegisters (state.register .address) state.heap)) := by
  change (executeOps rom op.relativeLower state).heap = Function.update state.heap
    (state.register .address + BitVec.ofNat bits (registerOffset op.target))
    (op.value (fun reg => state.heap
      (state.register .address + BitVec.ofNat bits (registerOffset reg))))
  cases op <;>
    simp [ValueOp.relativeLower, ValueOp.target, ValueOp.value, relativeRead, relativeWrite,
      executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeValue_base_prefix (op : ValueOp) (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) :
    (executeOps rom (op.relativeLower.take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 13
  · interval_cases count <;> cases op <;>
      simp [ValueOp.relativeLower, relativeRead, relativeWrite, executeOps, packingExecuteOp,
        wordOp, wordInstruction]
  · rw [List.take_of_length_le ((relativeValue_length op).trans (by omega))]
    cases op <;>
      simp [ValueOp.relativeLower, relativeRead, relativeWrite, executeOps, packingExecuteOp,
        wordOp, wordInstruction]

theorem relativeValue_prefix_frame (op : ValueOp) (rom : PhysicalROM) (state : WordState bits)
    (point : BitVec bits)
    (hne : point ≠ state.register .address + BitVec.ofNat bits (registerOffset op.target))
    (count : Nat) :
    (executeOps rom (op.relativeLower.take count) state).heap point = state.heap point := by
  by_cases hc : count ≤ 13
  · interval_cases count <;> cases op <;> simp only [ValueOp.target] at hne <;>
      simp [ValueOp.relativeLower, relativeRead, relativeWrite, executeOps,
        packingExecuteOp, wordOp, wordInstruction]
    all_goals exact Function.update_of_ne hne _ _
  · rw [List.take_of_length_le ((relativeValue_length op).trans (by omega)),
      relativeValue_heap, Function.update_of_ne hne]

theorem portRegisters_update (base : BitVec bits)
    (hi : Function.Injective (fun reg => base + BitVec.ofNat bits (registerOffset reg)))
    (heap : BitVec bits → BitVec bits) (target : Register) (value : BitVec bits) :
    portRegisters base
      (Function.update heap (base + BitVec.ofNat bits (registerOffset target)) value) =
      Function.update (portRegisters base heap) target value := by
  funext reg
  by_cases he : reg = target
  · subst reg
    simp only [portRegisters, Function.update_self]
  · have hn : base + BitVec.ofNat bits (registerOffset reg) ≠
        base + BitVec.ofNat bits (registerOffset target) := fun hh => he (hi hh)
    simp only [portRegisters, Function.update_of_ne hn, Function.update_of_ne he]

theorem relativeValue_simulation (op : ValueOp) (rom : PhysicalROM) (state : WordState bits)
    (hi : Function.Injective (fun reg =>
      state.register .address + BitVec.ofNat bits (registerOffset reg))) :
    portRegisters (state.register .address) (executeOps rom op.relativeLower state).heap =
      (wordOp rom op.original
        { state with register := portRegisters (state.register .address) state.heap }).register := by
  rw [relativeValue_heap, portRegisters_update _ hi, valueOp_original_registers]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
