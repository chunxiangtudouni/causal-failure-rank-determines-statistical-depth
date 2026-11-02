module

public import Structure.PSTR_HD_HeadsActualZeroProducer_129
public import Structure.PSTR_HD_HeadsZeroGivenQuerySafe_126
public import Structure.PSTR_HD_HeadsCodeFits_127

/-! ORIGINAL q0 heads branch from the real44-step query, with no query
producer or runtime numeric oracle assumed. Only fixed literal AST CodeAt,
code-word and length facts remain for the eventual one global query array.
Original w32/F8192 supplies every ROM, address and total footprint bound. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open RawTreePreprocessingClaims PaperProofs.Common.Native.CompactPrice

theorem zero_original_allocation (full : List (Finset (Fin 0))) :
    PSTRCountAllocation.allocation full = 8192 * (full.length + 1) + 4 := by
  simp only [PSTRCountAllocation.allocation, capacityWords, treeSize, ↓reduceIte, Nat.add_zero]
  exact PSTRZeroHeads.shared_heapWords full.length 32 8192 (by decide)

theorem zero_original_head_rooms (full : List (Finset (Fin 0))) :
    Fits (indexWidth 32 full.length 0) (46 + 10 + full.length) ∧
      46 + 10 + full.length < PSTRCountAllocation.allocation full := by
  have big := PSTRZeroHeads.shared_footprint_fit full.length 32 65536 (by decide) (by decide)
  refine ⟨(show 46 + 10 + full.length ≤ 65536 * (full.length + 1) + 127 by omega).trans_lt big, ?_⟩
  rw [zero_original_allocation]
  omega

theorem zero_original_heads_footprint (full : List (Finset (Fin 0))) (queryBody : List PackingOp)
    (hlen : queryBody.length ≤ 8192) :
    Fits (indexWidth 32 full.length 0) ((callInput 0 full .query).size + PSTRCountAllocation.allocation full +
      (packingCode (uniformHeadsProgram queryBody)).length) := by
  have big := PSTRZeroHeads.shared_footprint_fit full.length 32 65536 (by decide) (by decide)
  rw [PSTRCountAllocation.input_size, zero_original_allocation, uniform_heads_code_length]
  exact (show full.length * 0 + 3 + (8192 * (full.length + 1) + 4) + (5 * queryBody.length + 600) ≤
    65536 * (full.length + 1) + 127 by omega).trans_lt big

theorem actual_zero_heads_from_code (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (queryBody : List PackingOp) (zeroStart : Nat)
    (cb : PSTRUniformBootstrapCode.Contains (uniformHeadsProgram queryBody) zeroStart)
    (zs : PSTROuterCountCode.BlockAt (uniformHeadsProgram queryBody) zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt (uniformHeadsProgram queryBody) (zeroStart + 23)
      (PSTRCountControl.backBlock queryBody.length))
    (hlen : queryBody.length ≤ 8192) (literal : ∀ value ∈ packingCode queryBody, value < 65536)
    (heap : BitVec (indexWidth 32 full.length 0) → BitVec (indexWidth 32 full.length 0))
    (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap) :
    ∃ steps ≤ (full.length + 1) * 101,
      DynamicRunCorrect (PSTRCountAllocation.allocation full) (callInput 0 full .query) (uniformHeadsProgram queryBody) steps heap ∧
      callCost 0 full (uniformHeadsProgram queryBody) .query steps heap ≤
        (5 * queryBody.length + 2193) * headWork 0 full ∧
      (let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps (packingInitial heap);
        HeapRepresents 0 full 0 ⟨full.length, used, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords 0 full used).length ≤ PSTRCountAllocation.allocation full ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords 0 full used).length = headWords 0 full used) := by
  let bits := indexWidth 32 full.length 0
  have big := PSTRZeroHeads.shared_footprint_fit full.length 32 65536 (by decide) (by decide)
  have h65536 : Fits bits 65536 := (show 65536 ≤ 65536 * (full.length + 1) + 127 by omega).trans_lt big
  have body : WordsFit bits (packingCode queryBody) := fun value hv => (literal value hv).trans h65536
  have hpcfit := original_uniform_heads_pc_fit full.length 0 queryBody (hlen.trans (by decide : 8192 ≤ 65536))
  have hwords := uniform_heads_code_fit queryBody body hpcfit
  have producer := actual_zero_query_producer full used queryBody zeroStart cb zs bs hwords hpcfit
  have rooms := zero_original_head_rooms full
  have hrom : ∀ region, WordsFit bits ((callInput 0 full .query).words region) := by
    intro region value hv
    rw [PSTRZeroHeads.zero_query_rom] at hv
    cases region with
    | input =>
      simp only [PhysicalROM.words, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact (show full.length ≤ 46 + 10 + full.length by omega).trans_lt rooms.1
      · exact (show 0 ≤ 46 + 10 + full.length by omega).trans_lt rooms.1
      · exact (show 0 ≤ 46 + 10 + full.length by omega).trans_lt rooms.1
    | internal => cases hv
    | children => cases hv
  have hb : 8 ≤ bits := (PSTRZeroHeads.original_width_eight full.length).trans
    (PSTRZeroHeads.width_mono full.length 32 (by decide))
  obtain ⟨steps, hsteps, dynamic, cost, output⟩ := zero_heads_dynamic_given_actual_query full hl used
    (PSTRCountAllocation.allocation full) 44 44 queryBody producer hwords hpcfit hrom
    (zero_original_heads_footprint full queryBody hlen) heap hb rep rooms.1 rooms.2 (by simp [liveWork])
  refine ⟨steps, hsteps, dynamic, ?_, output⟩
  simpa only [show 12 * 44 + 5 * queryBody.length + 1665 = 5 * queryBody.length + 2193 by omega] using cost

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
