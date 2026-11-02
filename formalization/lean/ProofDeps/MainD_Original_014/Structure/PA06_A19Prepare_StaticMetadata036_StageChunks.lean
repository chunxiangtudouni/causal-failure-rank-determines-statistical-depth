module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageProgram

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual fetched prefixes of all non-query blocks of the fixed202 stage
producer. The frozen022 query has its separate real linked execution. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

theorem stage_chunk_run_prefix (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : StageCodeAt containing start) (chunk : StageChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + stageChunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ stageChunkLength chunk) :
    natRun rom containing count state = runOps rom ((stageChunkCode start chunk).take count) state := by
  rw [stage_chunk_split start chunk]
  refine natRun_segment_prefix rom containing (stageChunkLead start chunk) (stageChunkLast start chunk)
    (start + stageChunkOffset chunk)
    (by have hs := stage_chunk_span chunk; have hl := stage_chunk_lead_length start chunk; have hb := code.1; omega)
    ?_ ?_ (stage_chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := stage_chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := stage_chunk_lead_length start chunk
    have hpos : position < stageChunkLength chunk := by omega
    have hh := (code.2 (stageChunkOffset chunk + position) (by have hs := stage_chunk_span chunk; omega)).trans
      (stage_chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := stage_chunk_span chunk; have hb := code.1; omega),
      List.getD_eq_getElem _ _ (by rw [stage_chunk_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, stageChunkLead, List.getElem_take] using hh
  · have hlen := stage_chunk_lead_length start chunk
    have hpos : (stageChunkLead start chunk).length < stageChunkLength chunk := by omega
    have hh := (code.2 (stageChunkOffset chunk + (stageChunkLead start chunk).length)
      (by have hs := stage_chunk_span chunk; omega)).trans (stage_chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := stage_chunk_span chunk; have hb := code.1; omega)] at hh
    have heq : (stageChunkLead start chunk).length = stageChunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, stageChunkLast] using hh

theorem stage_chunk_run (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : StageCodeAt containing start) (chunk : StageChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + stageChunkOffset chunk)) (ha : state.halted = false) :
    natRun rom containing (stageChunkLength chunk) state = runOps rom (stageChunkCode start chunk) state := by
  rw [stage_chunk_run_prefix rom containing start code chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [stage_chunk_length])]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
