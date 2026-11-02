module

public import Structure.PSTR_HD_StaticLeaf_024
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! A fixed locator for count-kernel scratch immediately after ORIGINAL
metadata. Only address/total/flag are scratch: incoming node/index, leaf/value,
counts-base/old and child-offset/fresh are all preserved before spilling. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountWorkspace

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRStaticLayout PSTRStaticHeap

def base (q : Nat) (full : List (Finset (Fin q))) (capWords bits : Nat) : Nat :=
  7 + packedCapacityWords q capWords bits + 5 * (prepareNormalization q full).indexed.nodes.size +
    edgeCount q full + full.length + q

theorem base_metadata_end (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (capWords bits : Nat) :
    base q full capWords bits = metadataAddress q capWords bits (staticMetadata q full).length := by
  rw [metadata_length q full hq]
  unfold base metadataAddress physicalHeaderWords
  omega

def program : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.constant .flag 6)),
   .base (.base (.add .address .total .flag)),
   .base (.base (.loadHeap .flag .address)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.constant .address 0)),
   .base (.base (.loadHeap .flag .address)),
   .base (.base (.constant .address 5)),
   .arithmetic .multiply .flag .flag .address,
   .base (.base (.add .total .total .flag)),
   .base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .flag .address)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .flag .address)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.constant .flag 7)),
   .base (.base (.add .address .total .flag))]

theorem program_length : program.length = 19 := rfl
theorem program_straight : StraightProgram program := by simp [program, StraightProgram, StraightOp]
theorem code_length : (packingCode program).length = 100 := by rw [packingCode_length, program_length]

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  have hs : value < 256 := by
    simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact hs.trans_le hpow

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 95 < 2 ^ bits
  omega

theorem execute_base {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap) :
    let result := executeOps (callInput q full command) program state
    result.register .address = BitVec.ofNat bits (base q full capWords bits) ∧
    result.register .value = state.register .value ∧ result.register .index = state.register .index ∧
    result.register .old = state.register .old ∧ result.register .fresh = state.register .fresh ∧
    result.heap = state.heap ∧ result.halted = state.halted := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := by simp
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  have h5 : (BitVec.ofNat bits 5).toNat = 5 := Nat.mod_eq_of_lt (by omega)
  have ht0 := (headers full configuration capWords state.heap rep).1
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using ht0
  have htn : (BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size).toNat =
      (prepareNormalization q full).indexed.nodes.size := by
    rw [← ht]
    simpa only [treeSize, ne_of_gt hq, ite_false] using rep.1
  have hp := (headers full configuration capWords state.heap rep).2.2.1
  have hbase : BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 =
      BitVec.ofNat bits (metadataAddress q capWords bits 0) := by
    rw [BitVec.ofNat_add_ofNat]
    congr 1
    unfold metadataAddress physicalHeaderWords
    omega
  have he : state.heap (BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6) =
      BitVec.ofNat bits (edgeCount q full) := by
    rw [hbase]
    exact child_count_word full configuration capWords state.heap hq rep
  have hN : ((callInput q full command).words .input).getD 0 0 = full.length := rfl
  have hqword : ((callInput q full command).words .input).getD 1 0 = q := rfl
  have ha : BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits (edgeCount q full) +
      BitVec.ofNat bits ((prepareNormalization q full).indexed.nodes.size * 5) +
      BitVec.ofNat bits full.length + BitVec.ofNat bits q + BitVec.ofNat bits 7 =
        BitVec.ofNat bits (base q full capWords bits) := by
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    unfold base
    ring
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, ↓reduceIte, hp, ht, he, htn, h0, h1, h5, hN, hqword, ha]

theorem containing_base {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ containing.length)
    (hcode : ∀ i (hi : i < program.length), containing[start + i]'(by omega) = program[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom containing 19 state = executeOps rom program state := by
  exact PSTRWordSegments.straight_segment rom containing program start hbound hcode
    program_straight hwords hpcfit state hpc ha

theorem prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits < heapWords)
    (hb : 8 ≤ bits) (count : Nat) (hc : count < program.length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (program.take count) state) program[count] := by
  have hp := (headers full configuration capWords state.heap rep).2.2.1
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := by simp
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := by
    apply Nat.mod_eq_of_lt
    have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
    omega
  have hheap : 3 ≤ heapWords := by unfold base at hroom; omega
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have hchild : (BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6).toNat < heapWords := by
    rw [BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    unfold base at hroom
    omega
  have hinput : 1 < (callInput q full command).input.length := by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  change count < 19 at hc
  interval_cases count <;>
    simp_all +decide [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words] <;> omega

theorem inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom containing 19 state).length ≤ 228 :=
  packingDynamicTrace_length_le rom containing 19 state

end PaperProofs.Structure.LaminarTree.PSTRCountWorkspace
