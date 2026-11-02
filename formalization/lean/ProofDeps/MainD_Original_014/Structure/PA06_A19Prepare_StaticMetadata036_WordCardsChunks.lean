module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCardsNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED actual fetched-prefix safety for the four chunks of the
same84-op cards program. Numeric results are supplied only by the concrete
block proofs, then discharged from real cache data by WordCardsRun. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (loadRel storeRel setRel incrementRel RunFacts)

theorem cards_chunk_final_offset (rom : PhysicalROM) (start : Nat) (chunk : CardsChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + cardsChunkOffset chunk)) :
    ∃ offset ≤ 84, (runOps rom (cardsChunkCode start chunk) state).pc = 5 * (start + offset) := by
  cases chunk with
  | «initialize» =>
    refine ⟨4, by decide, ?_⟩
    change (runOps rom (setRel 19 0) state).pc = _
    have initializeLength : (setRel 19 0).length = 4 := rfl
    rw [runOps_pc rom _ state (by simp [setRel, storeRel, NoJump]), initializeLength, hpc]
    simp only [cardsChunkOffset, Nat.add_zero]
    omega
  | test =>
    have hp := scanBoundedTest_pc rom (state.register .address)
      (state.heap (state.register .address + 2)) (state.heap (state.register .address + 19))
      2 19 (start + 84) state rfl rfl rfl
    by_cases hz : state.heap (state.register .address + 2) - state.heap (state.register .address + 19) = 0
    · exact ⟨84, by decide, by change (runOps rom (scanBoundedTest 2 19 (start + 84)) state).pc = _; rw [hp, ite_eq_left hz]⟩
    · refine ⟨13, by decide, ?_⟩
      change (runOps rom (scanBoundedTest 2 19 (start + 84)) state).pc = _
      rw [hp, ite_eq_right hz, hpc]
      simp only [cardsChunkOffset]
      omega
  | body =>
    refine ⟨73, by decide, ?_⟩
    change (runOps rom cardsBody state).pc = _
    rw [runOps_pc rom _ state cardsBody_noJump, cardsBody_length, hpc]
    simp only [cardsChunkOffset]
    omega
  | tail =>
    refine ⟨4, by decide, ?_⟩
    simp [cardsChunkCode, cardsTail, incrementRel, loadRel, storeRel, jumpTo,
      runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem cards_chunk_prefix_pc (rom : PhysicalROM) (start : Nat) (chunk : CardsChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + cardsChunkOffset chunk))
    (count : Nat) (hc : count < cardsChunkLength chunk) :
    (runOps rom ((cardsChunkCode start chunk).take count) state).pc =
      5 * (start + cardsChunkOffset chunk + count) := by
  have hlen := cards_chunk_lead_length start chunk
  have hn : count ≤ (cardsChunkLead start chunk).length := by omega
  rw [cards_chunk_split, List.take_append_of_le_length hn,
    runOps_pc rom _ state (fun op hm => cards_chunk_lead_noJump start chunk op (List.mem_of_mem_take hm)),
    List.length_take_of_le hn, hpc]
  omega

theorem cards_chunk_safe (rom : PhysicalROM) (B H : Nat) (containing : List PackingOp) (start : Nat)
    (code : CardsCodeAt containing start) (chunk : CardsChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + cardsChunkOffset chunk)) (ha : state.halted = false)
    (numeric : NumericSafe B H rom (cardsChunkCode start chunk) state) :
    RunFacts B H rom containing (cardsChunkLength chunk) state := by
  constructor
  · constructor
    · intro count hc
      rw [cards_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
      refine ⟨numeric.1 count (by rw [cards_chunk_length]; exact hc),
        (runOps_halted rom _ state).trans ha, ?_⟩
      by_cases he : count = cardsChunkLength chunk
      · subst count
        rw [List.take_of_length_le (by rw [cards_chunk_length])]
        obtain ⟨offset, ho, hp⟩ := cards_chunk_final_offset rom start chunk state hpc
        exact ⟨start + offset, by have hb := code.1; omega, hp⟩
      · have hl : count < cardsChunkLength chunk := by omega
        exact ⟨start + cardsChunkOffset chunk + count,
          by have hs := cards_chunk_span chunk; have hb := code.1; omega,
          cards_chunk_prefix_pc rom start chunk state hpc count hl⟩
    · intro count hc
      rw [cards_chunk_run_prefix rom containing start code chunk state hpc ha count hc.le]
      have hi : start + cardsChunkOffset chunk + count < containing.length := by
        have hs := cards_chunk_span chunk
        have hb := code.1
        omega
      refine ⟨start + cardsChunkOffset chunk + count, hi,
        cards_chunk_prefix_pc rom start chunk state hpc count hc, ?_⟩
      have hh := (code.2 (cardsChunkOffset chunk + count) (by have hs := cards_chunk_span chunk; omega)).trans
        (cards_chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by rw [cards_chunk_length]; exact hc)] at hh
      have he : containing[start + cardsChunkOffset chunk + count] =
          (cardsChunkCode start chunk)[count]'(by rw [cards_chunk_length]; exact hc) := by
        simpa only [Nat.add_assoc] using hh
      rw [he]
      exact numeric.2 count (by rw [cards_chunk_length]; exact hc)
  · intro count hc
    rw [cards_chunk_run_prefix rom containing start code chunk state hpc ha count hc]
    cases chunk <;> dsimp only [cardsChunkLength] at hc <;> interval_cases count <;> rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
