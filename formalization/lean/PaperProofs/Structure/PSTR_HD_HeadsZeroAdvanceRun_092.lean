module

public import PaperProofs.Structure.PSTR_HD_HeadsZeroReturn_091

/-! q=0 uses the SAME8+3 actual declaration/backedge. Its real endpoint46
record survives; persistent stage/failed representation is proved directly
from ORIGINAL q0 heap cells, not from positive metadata or an oracle. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem zero_advance_query_entry {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (origin rank : Nat) (entries : List Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (recorded : RecordedHeads 46 0 rank entries state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (hnext : Fits bits (configuration.stage + 1)) (he : Fits bits (46 + 10 + entries.length)) :
    let after := packingRun (callInput 0 full .query) whole 11 state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents 0 full 0 (nextConfiguration 0 full configuration .correct) after.heap ∧
    RecordedHeads 46 0 rank entries after.heap := by
  dsimp only
  let rom := callInput 0 full .query
  let advanced := executeOps rom headsCorrect state
  have advanced_pc : advanced.pc = BitVec.ofNat bits (5 * (origin + 64)) := by
    change (executeOps rom headsCorrect state).pc = _
    rw [executeOps_pc rom headsCorrect state PSTRRuntimeAdvance.program_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have advanced_halt : advanced.halted = false := (executeOps_halted rom headsCorrect state).trans ha
  have run8 : packingRun rom whole 8 state = advanced :=
    containing_headsCorrect full whole (origin + 56) (by have h := tailAt_length origin; rw [headsCorrect_length]; omega)
      (headsCorrect_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have back := same_heap_query_jump rom whole (origin + 64)
    (by have h := tailAt_length origin; rw [jumpBack_length]; omega)
    (jumpBack_tail_code whole origin hbound hcode) hwords hpcfit advanced advanced_pc advanced_halt
  have hbefore : 4 + packedCapacityWords 0 0 bits < 46 := by rw [zero_packed_words bits (by omega)]; omega
  have advanced_recorded : RecordedHeads 46 0 rank entries advanced.heap := by
    apply recorded_of_query_frame 46 0 rank entries state.heap advanced.heap recorded he
    intro physical hf hphysical
    exact headsCorrect_prefix_frame full configuration 0 46 state rep hbefore
      ((show 46 ≤ 46 + 10 + entries.length by omega).trans_lt he) physical hf hphysical 8 (by decide)
  rw [show 11 = 8 + 3 from rfl, run_add, run8]
  refine ⟨back.1, back.2.1, ?_, ?_⟩
  · rw [back.2.2.1]
    exact zero_correct_rep full configuration state hb rep hnext
  · rw [back.2.2.1]
    exact advanced_recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
