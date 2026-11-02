module

public import PaperProofs.Structure.PSTR_UniformQueryRoom_123

/-! One fixed ALL-q actual QUERY CallClaims, with the charged terminal HALT.
Original declaration updates and preprocessing remain separate obligations. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformQueryClaims

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeEntry020

theorem actual_query {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (allowed : Allowed full configuration .query)
    (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 1,
      CallClaims 32768 q full (capacity full) (allocatedWords full)
        PSTRUniformQueryCode.program configuration .query steps heap := by
  let program := PSTRUniformQueryCode.program
  let rom := callInput q full .query
  have hwords := PSTRUniformQueryEmbeddings.program_words full.length q
  have hpcfit := PSTRUniformQueryEmbeddings.program_pc full.length q
  obtain ⟨steps, upper, result⟩ := PSTRUniformQuery.actual_query full configuration allowed hl
    program PSTRUniformQueryCode.self_contains hwords hpcfit (packingInitial heap) rfl rfl rep
  let before := packingRun rom program steps (packingInitial heap)
  have hp : before.pc = BitVec.ofNat (wordBits full) (5 * program.length) := by
    rw [PSTRUniformQueryCode.program_length]
    exact result.pc
  have halt := PSTRCountKernel.halt_at_exit rom program steps (packingInitial heap)
    hwords hpcfit result.active hp
  have heap_eq : (packingRun rom program (steps + 1) (packingInitial heap)).heap = before.heap := by
    have hh := congrArg (fun state : WordState (wordBits full) => state.heap) halt
    exact hh
  have dynamic : DynamicRunCorrect (allocatedWords full) rom program (steps + 1) heap := by
    refine ⟨hwords, ?_, PSTRUniformQueryRoom.footprint_fit full .query,
      congrArg WordState.halted halt, ?_⟩
    · have hb : 32 ≤ wordBits full := PSTROriginalCountRoom.word_lower full.length q
      exact PSTRLiveHeaderSafety.input_fit full .query (by omega)
        (PSTROriginalCountRoom.raw_rooms full.length q).1
        (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
    · intro clock hc
      by_cases hs : clock < steps
      · obtain ⟨active, pc, op, decoded, access⟩ := result.safe clock hs
        exact ⟨active, pc, by rw [decoded]; exact access⟩
      · have he : clock = steps := by omega
        subst clock
        exact PSTRCountAllocation.terminal_access rom program _ before hwords hpcfit hp result.active
  have cost : callCost q full program .query (steps + 1) heap ≤
      32768 * liveWork q (treeSize q full) := by
    have hs := upper.trans (PSTRUniformQuery.budget_bound full)
    have hw := PSTRUniformQueryRoom.work_pos full
    have trace := packingDynamicTrace_length_le rom program (steps + 1) (packingInitial heap)
    unfold callCost
    change 1 + (packingCode program).length + 8 +
      (packingDynamicTrace rom program (steps + 1) (packingInitial heap)).length ≤ _
    rw [PSTRUniformQueryCode.code_length]
    omega
  refine ⟨steps + 1, by omega, dynamic, cost, ?_, ?_, ?_, ?_⟩
  · change HeapRepresents q full (capacity full) configuration _
    rw [heap_eq]
    exact result.represents steps le_rfl
  · intro address ha _positive
    rw [heap_eq]
    exact result.table steps le_rfl address ha
  · intro clock hc _positive
    by_cases hs : clock ≤ steps
    · exact result.capacityBound clock hs
    · have he : clock = steps + 1 := by omega
      subst clock
      rw [heap_eq]
      exact result.capacityBound steps le_rfl
  · intro hcursor
    rw [halt]
    exact result.correct

end PaperProofs.Structure.LaminarTree.PSTRUniformQueryClaims
