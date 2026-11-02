module

public import PaperProofs.Structure.PSTR_HD_HeadsFinish_056
public import PaperProofs.Structure.PSTR_AdvanceHeap_016

/-! The heads tail reads the actual persistent stage and original raw N.
Its declaration update is the existing real8op stage bump on QUERY ROM;
there is no external .correct call or reset. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def stageProbe : List PackingOp :=
  [.base (.base (.constant .total 2)),
   .base (.base (.loadHeap .flag .total)),
   .base (.base (.constant .total 4)),
   .base (.base (.add .flag .flag .total)),
   .base (.base (.loadHeap .old .flag)),
   .base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .index .index))]

def headsCorrect : List PackingOp := PSTRRuntimeAdvance.program

theorem stageProbe_length : stageProbe.length = 7 := rfl

theorem headsCorrect_length : headsCorrect.length = 8 := rfl

theorem stageProbe_straight : StraightProgram stageProbe := by simp [stageProbe, StraightProgram, StraightOp]

theorem execute_stageProbe {bits : Nat} (rom : PhysicalROM) (packed current N : Nat) (state : WordState bits)
    (hp : state.heap (BitVec.ofNat bits 2) = BitVec.ofNat bits packed)
    (hs : state.heap (BitVec.ofNat bits (4 + packed)) = BitVec.ofNat bits current)
    (hN : (rom.words .input).getD 0 0 = N) :
    let after := executeOps rom stageProbe state
    after.register .old = BitVec.ofNat bits current ∧ after.register .index = BitVec.ofNat bits N ∧
      after.register .value = state.register .value ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  change (rom.words .input)[0]?.getD 0 = N at hN
  have hc : packed + 4 = 4 + packed := by omega
  simp +decide [stageProbe, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hs, hN, BitVec.ofNat_add_ofNat, hc]

theorem query_stageProbe {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) :
    let after := executeOps (callInput q full .query) stageProbe state
    after.register .old = BitVec.ofNat bits configuration.stage ∧ after.register .index = BitVec.ofNat bits full.length ∧
      after.register .value = state.register .value ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  exact execute_stageProbe (callInput q full .query) (packedCapacityWords q capWords bits) configuration.stage full.length state
    (PSTRStaticHeap.headers full configuration capWords state.heap rep).2.2.1
    (by simpa only [physicalHeaderWords] using (PSTRStaticHeap.stage_failed full configuration capWords state.heap hq rep).1)
    rfl

theorem stageProbe_prefix_access {bits q : Nat} (full : List (Finset (Fin q)))
    (packed heapWords : Nat) (state : WordState bits)
    (hp : state.heap (BitVec.ofNat bits 2) = BitVec.ofNat bits packed) (hroom : 4 + packed < heapWords)
    (count : Nat) (hc : count < stageProbe.length) :
    packingAccessFits (callInput q full .query) heapWords
      (executeOps (callInput q full .query) (stageProbe.take count) state) stageProbe[count] := by
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have hs : (BitVec.ofNat bits (4 + packed)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  have hi : 0 < (callInput q full .query).input.length := by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hcomm : packed + 4 = 4 + packed := by omega
  change count < 7 at hc
  interval_cases count <;>
    simp_all +decide [stageProbe, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words, BitVec.ofNat_add_ofNat]

theorem headsCorrect_heap {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (rep : HeapRepresents q full capWords configuration state.heap) :
    (executeOps (callInput q full .query) headsCorrect state).heap =
      PSTRRuntimeAdvance.bumpHeap (packedCapacityWords q capWords bits) state.heap :=
  PSTRRuntimeAdvance.execute_heap (callInput q full .query) state _ rep.2.2.1

theorem headsCorrect_rep {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1)) :
    HeapRepresents q full capWords (nextConfiguration q full configuration .correct)
      (executeOps (callInput q full .query) headsCorrect state).heap := by
  rw [headsCorrect_heap full configuration capWords state rep]
  exact PSTRAdvanceHeap.heapRepresents_advance full configuration capWords state.heap hb hq rep bitmap hr hi hnext

theorem headsCorrect_prefix_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords endpoint : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hbefore : 4 + packedCapacityWords q capWords bits < endpoint) (he : Fits bits endpoint)
    (physical : Nat) (hf : Fits bits physical) (hp : endpoint ≤ physical)
    (count : Nat) (hc : count ≤ headsCorrect.length) :
    (executeOps (callInput q full .query) (headsCorrect.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  change (executeOps (callInput q full .query) (PSTRRuntimeAdvance.program.take count) state).heap (BitVec.ofNat bits physical) = _
  rw [PSTRRuntimeAdvance.prefix_heap (callInput q full .query) state _ rep.2.2.1 count hc]
  split
  · rfl
  · apply PSTRRuntimeAdvance.heap_frame
    exact (ofNat_injective_of_fit _ _ hf (hbefore.trans he)).not.mpr (by omega)

theorem containing_stageProbe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + stageProbe.length ≤ whole.length)
    (hcode : ∀ i (hi : i < stageProbe.length), whole[start + i]'(by omega) = stageProbe[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 7 state = executeOps rom stageProbe state :=
  straight_segment rom whole stageProbe start hbound hcode stageProbe_straight hwords hpcfit state hp ha

theorem containing_headsCorrect {bits q : Nat} (full : List (Finset (Fin q))) (whole : List PackingOp) (start : Nat)
    (hbound : start + headsCorrect.length ≤ whole.length)
    (hcode : ∀ i (hi : i < headsCorrect.length), whole[start + i]'(by omega) = headsCorrect[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun (callInput q full .query) whole 8 state = executeOps (callInput q full .query) headsCorrect state :=
  straight_segment _ whole headsCorrect start hbound hcode PSTRRuntimeAdvance.program_straight hwords hpcfit state hp ha

theorem headsCorrect_trace_bound {bits q : Nat} (full : List (Finset (Fin q))) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace (callInput q full .query) whole 8 state).length ≤ 96 := packingDynamicTrace_length_le _ whole 8 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
