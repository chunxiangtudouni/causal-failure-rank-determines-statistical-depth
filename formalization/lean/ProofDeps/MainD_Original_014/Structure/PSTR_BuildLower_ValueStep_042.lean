module

public import Structure.PSTR_BuildLower_BuilderRoom_039

/-! Actual inline literal ALU calls with VM-bank separation derived from
six static address bits. No caller injectivity/answer/cost premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ValueStep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

theorem bank_injective (base : BitVec bits) (hb : 6 ≤ bits) :
    Function.Injective (fun reg => base + BitVec.ofNat bits (registerOffset reg)) := by
  have hpow : 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hsmall (reg : Register) : registerOffset reg < 2 ^ bits :=
    lt_of_lt_of_le ((registerSlot_bounds reg).2.trans_le (by decide : 39 ≤ 64)) hpow
  intro left right hh
  apply registerSlot_injective
  change registerOffset left = registerOffset right
  have he := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp hh)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hsmall left), Nat.mod_eq_of_lt (hsmall right)] using he

theorem run (op : ValueOp) (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits bits (5 * (left ++ op.relativeLower ++ right).length)) :
    packingRun rom (left ++ op.relativeLower ++ right) op.relativeLower.length state =
      executeOps rom op.relativeLower state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append]; omega)
    (PA17UniformGenerator035a.segment_index left op.relativeLower right) (relativeValue_straight op)
    hcode hpcfit state hpc ha

theorem call (op : ValueOp) (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (hb : 6 ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits bits (5 * (left ++ op.relativeLower ++ right).length)) :
    let after := packingRun rom (left ++ op.relativeLower ++ right) op.relativeLower.length state
    op.relativeLower.length ≤ 13 ∧
    portRegisters (state.register .address) after.heap =
      (wordOp rom op.original {state with register := portRegisters (state.register .address) state.heap}).register ∧
    after.pc = BitVec.ofNat bits (5 * (left.length + op.relativeLower.length)) ∧
    after.halted = false ∧ after.register .address = state.register .address ∧
    ∀ point : BitVec bits, point ≠ state.register .address + BitVec.ofNat bits (registerOffset op.target) →
      after.heap point = state.heap point := by
  dsimp only
  rw [run op rom left right state hpc ha hcode hpcfit]
  refine ⟨relativeValue_length op, relativeValue_simulation op rom state (bank_injective _ hb), ?_,
    (executeOps_halted rom _ state).trans ha, ?_, ?_⟩
  · have he : 5 * left.length + 5 * op.relativeLower.length = 5 * (left.length + op.relativeLower.length) := by omega
    rw [executeOps_pc rom _ state (relativeValue_straight op), hpc, BitVec.ofNat_add_ofNat, he]
  · have hh := relativeValue_base_prefix op rom state op.relativeLower.length
    simpa only [List.take_length] using hh
  · intro point hne
    have hh := relativeValue_prefix_frame op rom state point hne op.relativeLower.length
    simpa only [List.take_length] using hh

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ValueStep
