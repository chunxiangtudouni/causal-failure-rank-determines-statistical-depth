module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED fetched-prefix adapter for the original202 stage chunks.
Every interior fetch uses the existing actual stage slice and no-jump
prefix. A chunk's actual final PC is supplied by its concrete effect lemma
at each local call, rather than by a new original-caller safety oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (RunFacts)
open PA17UniformGenerator035j (NumericSafe)

theorem stage_chunk_prefix_pc (rom : PhysicalROM) (start : Nat) (chunk : StageChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + stageChunkOffset chunk))
    (count : Nat) (hc : count < stageChunkLength chunk) :
    (runOps rom ((stageChunkCode start chunk).take count) state).pc =
      5 * (start + stageChunkOffset chunk + count) := by
  have hlen := stage_chunk_lead_length start chunk
  have hn : count ≤ (stageChunkLead start chunk).length := by omega
  rw [stage_chunk_split, List.take_append_of_le_length hn,
    runOps_pc rom _ state (fun op hm => stage_chunk_lead_noJump start chunk op (List.mem_of_mem_take hm)),
    List.length_take_of_le hn, hpc]
  omega

/-- NumericSafe and the concrete final-PC effect are local chunk results.
The actual stage code supplies all fetched operations; this adapter proves
their access/PC bounds and the unchanged hardwareCB at every prefix. -/
theorem stage_chunk_safe_at (rom : PhysicalROM) (B H : Nat)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (chunk : StageChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + stageChunkOffset chunk)) (ha : state.halted = false)
    (numeric : NumericSafe B H rom (stageChunkCode start chunk) state)
    (endOffset : Nat) (hend : endOffset ≤ 202)
    (hfinal : (runOps rom (stageChunkCode start chunk) state).pc = 5 * (start + endOffset)) :
    RunFacts B H rom containing (stageChunkLength chunk) state := by
  constructor
  · constructor
    · intro count hc
      rw [stage_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
      refine ⟨numeric.1 count (by rw [stage_chunk_length]; exact hc),
        (runOps_halted rom _ state).trans ha, ?_⟩
      by_cases he : count = stageChunkLength chunk
      · subst count
        rw [List.take_of_length_le (by rw [stage_chunk_length])]
        exact ⟨start + endOffset, by have hb := code.1; omega, hfinal⟩
      · have hl : count < stageChunkLength chunk := by omega
        exact ⟨start + stageChunkOffset chunk + count,
          by have hs := stage_chunk_span chunk; have hb := code.1; omega,
          stage_chunk_prefix_pc rom start chunk state hpc count hl⟩
    · intro count hc
      rw [stage_chunk_run_prefix rom containing start code chunk state hpc ha count hc.le]
      have hi : start + stageChunkOffset chunk + count < containing.length := by
        have hs := stage_chunk_span chunk
        have hb := code.1
        omega
      refine ⟨start + stageChunkOffset chunk + count, hi,
        stage_chunk_prefix_pc rom start chunk state hpc count hc, ?_⟩
      have hh := (code.2 (stageChunkOffset chunk + count) (by have hs := stage_chunk_span chunk; omega)).trans
        (stage_chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by rw [stage_chunk_length]; exact hc)] at hh
      have he : containing[start + stageChunkOffset chunk + count] =
          (stageChunkCode start chunk)[count]'(by rw [stage_chunk_length]; exact hc) := by
        simpa only [Nat.add_assoc] using hh
      rw [he]
      exact numeric.2 count (by rw [stage_chunk_length]; exact hc)
  · intro count hc
    rw [stage_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
    cases chunk <;> dsimp only [stageChunkLength] at hc <;> interval_cases count <;> rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
