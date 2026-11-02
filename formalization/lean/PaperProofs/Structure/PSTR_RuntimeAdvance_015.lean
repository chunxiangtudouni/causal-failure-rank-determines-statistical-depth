module

public import PaperProofs.Structure.PSTR_RuntimePackedRead_008

/-! Fixed physical stage increment from the real A19 header and stage word.
No current stage or pointer is supplied in the call ROM. All operations are
the original ISA, and all stores occur only at the actual stage address. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeAdvance

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def program : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .fresh 4)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .value .value .fresh)),
   .base (.base (.storeHeap .index .value))]

def bumpHeap {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  let pointer := BitVec.ofNat bits (4 + packed)
  Function.update heap pointer (heap pointer + BitVec.ofNat bits 1)

theorem program_length : program.length = 8 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem code_length : (packingCode program).length = 45 := by
  rw [packingCode_length, program_length]

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 40 < 2 ^ bits
  omega

theorem header_word {bits : Nat} (state : WordState bits) (packed : Nat)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed) :
    state.heap (BitVec.ofNat bits 2) = BitVec.ofNat bits packed := by
  have he := congrArg (BitVec.ofNat bits) hh
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed) :
    (executeOps rom program state).heap = bumpHeap packed state.heap := by
  have hc : packed + 4 = 4 + packed := by omega
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, header_word state packed hh,
    BitVec.ofNat_add_ofNat, hc, bumpHeap]

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (count : Nat) (hc : count ≤ 8) :
    (executeOps rom (program.take count) state).heap =
      if count < 8 then state.heap else bumpHeap packed state.heap := by
  by_cases hlt : count < 8
  · rw [ite_eq_left hlt]
    interval_cases count <;> rfl
  · have he : count = 8 := by omega
    subst count
    rw [ite_eq_right (by decide), show 8 = program.length from rfl, List.take_length]
    exact execute_heap rom state packed hh

theorem stage_word {bits : Nat} (packed current : Nat) (heap : BitVec bits → BitVec bits)
    (hc : (heap (BitVec.ofNat bits (4 + packed))).toNat = current)
    (hnext : Fits bits (current + 1)) :
    ((bumpHeap packed heap) (BitVec.ofNat bits (4 + packed))).toNat = current + 1 := by
  have he := congrArg (BitVec.ofNat bits) hc
  have hv : heap (BitVec.ofNat bits (4 + packed)) = BitVec.ofNat bits current := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  simp only [bumpHeap, Function.update_self, hv, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnext]

theorem heap_frame {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (4 + packed)) :
    bumpHeap packed heap address = heap address := by
  exact Function.update_of_ne hne _ _

theorem actual_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (hb : 8 ≤ bits) (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 9 state
    after.halted = true ∧ after.heap = bumpHeap packed state.heap := by
  dsimp only
  rw [show 9 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
  exact ⟨rfl, execute_heap rom state packed hh⟩

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 9 state).length ≤ 108 :=
  packingDynamicTrace_length_le rom program 9 state

end PaperProofs.Structure.LaminarTree.PSTRRuntimeAdvance
