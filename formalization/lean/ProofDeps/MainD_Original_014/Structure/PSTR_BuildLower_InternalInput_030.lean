module

public import Structure.PSTR_BuildLower_StageInput_029

/-! Actual .internal replacement reads the real copied parent cache and
real produced degree cache. The latter's representation is to be discharged
by A06 children-cache output, never by a supplied original tree-ROM answer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalInput
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

def code (pointer : Register) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++ relativeRead 528 .total ++ relativeRead 2 .value ++
    [.base (.base (.constant .fresh 4)), .arithmetic .multiply .index .total .fresh,
     .base (.base (.constant .fresh 533)), .base (.base (.add .index .index .fresh)),
     .base (.base (.add .index .address .index)), .base (.base (.add .index .index .old)),
     .base (.subtract .flag .value .old), .base (.subtract .old .old .value),
     .base (.base (.constant .value 5)), .arithmetic .multiply .fresh .total .value,
     .base (.base (.constant .value 533)), .base (.base (.add .fresh .fresh .value)),
     .base (.base (.add .fresh .address .fresh)), .base (.base (.add .fresh .fresh .old)),
     .base (.base (.select .index .flag .index .fresh)), .base (.base (.loadHeap .value .index))]

theorem code_length (pointer : Register) : (code pointer).length = 25 := rfl

theorem code_straight (pointer : Register) : StraightProgram (code pointer) := by
  simp [code, relativeRead, StraightProgram, StraightOp]

def targetAddress (state : WordState bits) (pointer : Register) : BitVec bits :=
  let a := Ordinary.pointerValue state pointer
  let M := state.heap (state.register .address + BitVec.ofNat bits 528)
  let t := state.heap (state.register .address + BitVec.ofNat bits 2)
  if a.toNat < t.toNat then
    state.register .address + (packingArithmetic .multiply M (BitVec.ofNat bits 4) + BitVec.ofNat bits 533) + a
  else state.register .address + (packingArithmetic .multiply M (BitVec.ofNat bits 5) + BitVec.ofNat bits 533) +
    BitVec.ofNat bits (a.toNat - t.toNat)

theorem value (rom : PhysicalROM) (pointer : Register) (state : WordState bits) :
    (executeOps rom (code pointer) state).register .value = state.heap (targetAddress state pointer) := by
  have hd : (state.heap (state.register .address + BitVec.ofNat bits 2)).toNat -
      (Ordinary.pointerValue state pointer).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (state.heap _).isLt
  unfold Ordinary.pointerValue at hd
  simp [code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    targetAddress, Ordinary.pointerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
    Nat.sub_eq_zero_iff_le, BitVec.add_assoc]
  simp only [← Nat.not_lt, ite_not]

theorem prefix_frame (rom : PhysicalROM) (pointer : Register) (state : WordState bits) (count : Nat) :
    (executeOps rom ((code pointer).take count) state).heap = state.heap ∧
      (executeOps rom ((code pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 25
  · interval_cases count <;>
      simp [code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [code_length]; omega)]
    exact ⟨rfl, rfl⟩

theorem run (rom : PhysicalROM) (pointer : Register) (left right : List PackingOp)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code pointer ++ right).length)) :
    packingRun rom (left ++ code pointer ++ right) 25 state = executeOps rom (code pointer) state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, code_length]; omega)
    (PA17UniformGenerator035a.segment_index left (code pointer) right) (code_straight pointer)
    hcode hpcfit state hpc ha

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalInput
