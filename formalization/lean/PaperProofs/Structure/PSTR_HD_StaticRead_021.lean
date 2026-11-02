module

public import PaperProofs.Structure.PSTR_HD_StaticHeap_020
public import PaperProofs.Structure.PSTR_HD_WordSegments_014
import Mathlib.Tactic.IntervalCases

/-! A fixed six-instruction metadata reader. Its index register is computed
by preceding runtime code; no stage/tree/answer field is added to callInput.
The actual packed-size header is loaded from the persistent heap. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRStaticRead

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRStaticLayout PSTRStaticHeap

variable {bits q : Nat}

def program : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.constant .old 6)),
   .base (.base (.add .address .total .old)),
   .base (.base (.add .address .address .index)),
   .base (.base (.loadHeap .value .address))]

theorem program_length : program.length = 6 := rfl

theorem code_length : (packingCode program).length = 35 := by rw [packingCode_length, program_length]

theorem program_straight : StraightProgram program := by simp [program, StraightProgram, StraightOp]

theorem code_fit (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  have hs : value < 256 := by
    simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact hs.trans_le hpow

theorem pc_fit (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 30 < 2 ^ bits
  omega

theorem execute_read (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (position : Nat) (hp : position < (staticMetadata q full).length)
    (hi : state.register .index = BitVec.ofNat bits position) :
    let result := executeOps rom program state
    result.register .value = BitVec.ofNat bits (staticMetadata q full)[position] ∧
    result.register .address = BitVec.ofNat bits (metadataAddress q capWords bits position) ∧
    result.register .index = state.register .index ∧
    result.register .fresh = state.register .fresh ∧
    result.register .flag = state.register .flag ∧ result.heap = state.heap := by
  have hh := (PSTRStaticHeap.headers full configuration capWords state.heap rep).2.2.1
  have hv := metadata_word full configuration capWords state.heap hq rep position hp
  have ha : BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 +
      BitVec.ofNat bits position = BitVec.ofNat bits (metadataAddress q capWords bits position) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1
    unfold metadataAddress physicalHeaderWords
    omega
  simp +decide [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hh, hi, ha, hv]

theorem prefix_access (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (position : Nat) (hi : state.register .index = BitVec.ofNat bits position)
    (hh : 3 ≤ heapWords) (hroom : metadataAddress q capWords bits position < heapWords)
    (count : Nat) (hc : count < program.length) :
    packingAccessFits rom heapWords (executeOps rom (program.take count) state) program[count] := by
  have hhead := (PSTRStaticHeap.headers full configuration capWords state.heap rep).2.2.1
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords :=
    (Nat.mod_le 2 (2 ^ bits)).trans_lt (by omega)
  have ha : (BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 +
      BitVec.ofNat bits position).toNat < heapWords := by
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    unfold metadataAddress physicalHeaderWords at hroom
    omega
  change count < 6 at hc
  interval_cases count <;>
    simp_all +decide [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits]

/-- Literal embedding has no intermediate HALT; a containing caller pays
the real six fetched instructions and keeps its original continuation. -/
theorem containing_run (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ containing.length)
    (hcode : ∀ i (hi : i < program.length), containing[start + i]'(by omega) = program[i])
    (hwords : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom containing 6 state = executeOps rom program state := by
  exact PSTRWordSegments.straight_segment rom containing program start hbound hcode
    program_straight hwords hpcfit state hpc ha

theorem inline_trace_bound (rom : PhysicalROM) (containing : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom containing 6 state).length ≤ 72 :=
  packingDynamicTrace_length_le rom containing 6 state

theorem standalone_read (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (position : Nat) (hp : position < (staticMetadata q full).length)
    (hi : state.register .index = BitVec.ofNat bits position)
    (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let result := packingRun rom program 7 state
    result.halted = true ∧ result.register .value = BitVec.ofNat bits (staticMetadata q full)[position] ∧
      result.heap = state.heap := by
  rw [show 7 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom program state program_straight (code_fit hb) (pc_fit hb) hpc ha]
  have hr := execute_read rom full configuration capWords state hq rep position hp hi
  exact ⟨rfl, hr.1, hr.2.2.2.2.2⟩

theorem original_address_room (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (capWords indexFactor : Nat) (hi : 8 ≤ indexFactor)
    (position : Nat) (hp : position < (staticMetadata q full).length) :
    metadataAddress q capWords bits position <
      physicalHeaderWords + packedCapacityWords q capWords bits +
        indexFactor * (full.length + q + treeSize q full + 1) := by
  have hroom := metadata_index_room q full hq hl indexFactor hi
  unfold metadataAddress
  omega

end PaperProofs.Structure.LaminarTree.PSTRStaticRead
