module

public import PaperProofs.Structure.PSTR_HD_CountSlots_050
public import PaperProofs.Structure.PSTR_QueryLayout_041

/-! Actual read-only endpoint addressing for the ONE-body heads controller.
Only address/total/flag are scratch; the real query's4 reply registers survive. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open PSTRCountKernel PSTRCountWorkspace PSTRStaticHeap PSTRWordSegments

def endpoint {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) : Nat :=
  PSTRQueryLayout.endpoint (base q full capWords bits) (treeSize q full) q

def outputBase (endpoint : Nat) : Nat := endpoint + 8

def endpointTail : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.loadHeap .flag .total)),
   .base (.base (.constant .total 3)),
   .arithmetic .multiply .flag .flag .total,
   .base (.base (.add .address .address .flag)),
   .base (.base (.constant .total 1)),
   .base (.base (.loadROM .input .flag .total)),
   .base (.base (.constant .total 2)),
   .arithmetic .multiply .flag .flag .total,
   .base (.base (.add .address .address .flag)),
   .base (.base (.constant .total 40)),
   .base (.base (.add .address .address .total))]

def endpointProgram : List PackingOp := PSTRCountWorkspace.program ++ endpointTail

theorem endpointTail_length : endpointTail.length = 12 := rfl

theorem endpointProgram_length : endpointProgram.length = 31 := rfl

theorem endpointProgram_straight : StraightProgram endpointProgram := by
  simp [endpointProgram, PSTRCountWorkspace.program, endpointTail, StraightProgram, StraightOp]

theorem endpointProgram_readOnly : ∀ op ∈ endpointProgram, ReadOnly op := by
  simp [endpointProgram, PSTRCountWorkspace.program, endpointTail, ReadOnly]

theorem endpointProgram_code_length : (packingCode endpointProgram).length = 160 := by
  rw [packingCode_length, endpointProgram_length]

theorem endpointProgram_code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode endpointProgram) := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  intro value hv
  have hs : value < 256 := by
    simp [packingCode, endpointProgram, PSTRCountWorkspace.program, endpointTail,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
      Register.word, Region.word, haltWords] at hv
    omega
  exact hs.trans_le hp

theorem endpointProgram_pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * endpointProgram.length) := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  change 155 < 2 ^ bits
  omega

theorem execute_endpointTail {bits : Nat} (rom : PhysicalROM) (workspace tree q : Nat)
    (state : WordState bits) (hb : 8 ≤ bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits tree)
    (htn : (BitVec.ofNat bits tree).toNat = tree) (hqfit : Fits bits q)
    (hraw : (rom.words .input).getD 1 0 = q) :
    let after := executeOps rom endpointTail state
    after.register .address = BitVec.ofNat bits (workspace + tree * 3 + q * 2 + 40) ∧
      after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
      after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
      after.heap = state.heap ∧ after.halted = state.halted := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat bits 2).toNat = 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := Nat.mod_eq_of_lt (by omega)
  have hqn : (BitVec.ofNat bits q).toNat = q := Nat.mod_eq_of_lt hqfit
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp +decide only [endpointTail, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, ↓reduceIte, ha, ht, htn, h1, h2, h3,
    hqn, hraw, BitVec.ofNat_add_ofNat]

theorem execute_endpoint {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hqfit : Fits bits q)
    (rep : HeapRepresents q full capWords configuration state.heap) :
    let after := executeOps (callInput q full command) endpointProgram state
    after.register .address = BitVec.ofNat bits (endpoint full capWords bits) ∧
      after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
      after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
      after.heap = state.heap ∧ after.halted = state.halted := by
  dsimp only
  let located := executeOps (callInput q full command) PSTRCountWorkspace.program state
  have located_result := execute_base full command configuration capWords state hb hq rep
  have ht : located.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (treeSize q full) := by
    rw [located_result.2.2.2.2.2.1]
    exact (headers full configuration capWords state.heap rep).1
  have htn : (BitVec.ofNat bits (treeSize q full)).toNat = treeSize q full := by
    rw [← (headers full configuration capWords state.heap rep).1]
    exact rep.1
  have hraw : ((callInput q full command).words .input).getD 1 0 = q := rfl
  have he : base q full capWords bits + treeSize q full * 3 + q * 2 + 40 = endpoint full capWords bits := by
    unfold endpoint
    rw [PSTRQueryLayout.endpoint_eq]
    ring
  have tail := execute_endpointTail (callInput q full command) (base q full capWords bits)
    (treeSize q full) q located hb located_result.1 ht htn hqfit hraw
  rw [endpointProgram, executeOps_append]
  exact ⟨tail.1.trans (congrArg (BitVec.ofNat bits) he), tail.2.1.trans located_result.2.1,
    tail.2.2.1.trans located_result.2.2.2.1, tail.2.2.2.1.trans located_result.2.2.2.2.1,
    tail.2.2.2.2.1.trans located_result.2.2.1,
    tail.2.2.2.2.2.1.trans located_result.2.2.2.2.2.1,
    tail.2.2.2.2.2.2.trans located_result.2.2.2.2.2.2⟩

theorem endpoint_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (endpointProgram.take count) state).heap = state.heap :=
  readOnly_prefix_heap rom endpointProgram state endpointProgram_readOnly count

theorem endpointTail_prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits) (hh : 0 < heapWords)
    (count : Nat) (hc : count < endpointTail.length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (endpointTail.take count) state) endpointTail[count] := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := by simp
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  have hin : 1 < (callInput q full command).input.length := by
    simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  change count < 12 at hc
  interval_cases count <;>
    simp_all +decide [endpointTail, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words]

theorem endpoint_prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits < heapWords) (count : Nat) (hc : count < endpointProgram.length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (endpointProgram.take count) state) endpointProgram[count] := by
  have hstart := PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep hroom hb
  have p0 := readOnly_prefixOK (callInput q full command) heapWords (fun _ => True)
    PSTRCountWorkspace.program state locator_readOnly hstart
  have p1 := readOnly_prefixOK (callInput q full command) heapWords (fun _ => True) endpointTail
    (executeOps (callInput q full command) PSTRCountWorkspace.program state)
    (by simp [endpointTail, ReadOnly]) (endpointTail_prefix_access full command heapWords _ hb (by unfold base at hroom; omega))
  exact (prefixOK_append _ _ _ _ _ _ p0 p1).access count hc

theorem containing_endpoint {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + endpointProgram.length ≤ whole.length)
    (hcode : ∀ i (hi : i < endpointProgram.length), whole[start + i]'(by omega) = endpointProgram[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 31 state = executeOps rom endpointProgram state :=
  straight_segment rom whole endpointProgram start hbound hcode endpointProgram_straight hwords hpcfit state hp ha

theorem endpoint_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 31 state).length ≤ 372 := packingDynamicTrace_length_le rom whole 31 state

theorem heads_room {bits q : Nat} (full : List (Finset (Fin q))) (capWords indexFactor : Nat)
    (hq : 0 < q) (hl : LaminarSchedule full) (hi : 128 ≤ indexFactor) :
    endpoint full capWords bits + full.length + 10 < physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1) := by
  have he := PSTRQueryLayout.endpoint_index64 full capWords bits hq hl
  have hw : base q full capWords bits = PSTRQueryLayout.physicalWorkspace full capWords bits :=
    base_metadata_end q full hq capWords bits
  rw [← hw] at he
  have hm := Nat.mul_le_mul_right (full.length + q + treeSize q full + 1) hi
  unfold endpoint
  omega

theorem heads_room8192 {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (hq : 0 < q) (hl : LaminarSchedule full) :
    endpoint full capWords bits + full.length + 10 < physicalHeaderWords + packedCapacityWords q capWords bits +
      8192 * (full.length + q + treeSize q full + 1) := heads_room full capWords 8192 hq hl (by decide)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
