module

public import Structure.PSTR_HD_HeadsOriginalFootprint_132

/-! CONDITIONAL INTERNAL positive-query consumer with ALL original numeric
premises discharged by w32/F8192. Only the still-to-be-constructed actual
same-body producer and static literal AST facts remain. This is not an
existence theorem or original HeadExtraction/FullClaims. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open RawTreePreprocessingClaims PaperProofs.Common.Native.CompactPrice

theorem original_positive_heads_given_actual_query {q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (used : Finset (Fin q))
    (queryBody : List PackingOp) (budget constant : Nat)
    (producer : InternalQueryProducer full used (capacityWords 8192 full.length q (treeSize q full))
      (PSTRCountAllocation.allocation full) budget queryBody (bits := indexWidth 32 full.length q))
    (hlen : queryBody.length ≤ 8192) (literal : ∀ value ∈ packingCode queryBody, value < 65536)
    (hbudget : budget ≤ constant * liveWork q (treeSize q full))
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) ⟨0, used, false⟩ heap) :
    ∃ steps ≤ (full.length + 1) * (budget + 88),
      DynamicRunCorrect (PSTRCountAllocation.allocation full) (callInput q full .query) (uniformHeadsProgram queryBody) steps heap ∧
      callCost q full (uniformHeadsProgram queryBody) .query steps heap ≤
        (12 * constant + 5 * queryBody.length + 1665) * headWork q full ∧
      (let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps (packingInitial heap);
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) ⟨full.length, used, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords q full used).length ≤ PSTRCountAllocation.allocation full ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords q full used).length = headWords q full used) := by
  let bits := indexWidth 32 full.length q
  let cap := capacityWords 8192 full.length q (treeSize q full)
  let E := endpoint full cap bits
  have hsmall : Fits bits 65536 := by
    apply PA17PackingBounds043.polynomial_fits
    have hpowers := PA17PackingBounds043.powers_le_six full.length q
    omega
  have body : WordsFit bits (packingCode queryBody) := fun value hv => (literal value hv).trans hsmall
  have hpcfit := original_uniform_heads_pc_fit full.length q queryBody (hlen.trans (by decide : 8192 ≤ 65536))
  have hwords := uniform_heads_code_fit queryBody body hpcfit
  have hfoot := original_heads_total_footprint full .query queryBody hlen
  have halloc : Fits bits (PSTRCountAllocation.allocation full) :=
    (show PSTRCountAllocation.allocation full ≤ (callInput q full .query).size + PSTRCountAllocation.allocation full +
      (packingCode (uniformHeadsProgram queryBody)).length by omega).trans_lt hfoot
  have hroom : E + 10 + full.length < PSTRCountAllocation.allocation full := by
    have h := heads_room8192 full cap hq hl (bits := bits)
    change E + full.length + 10 < PSTRCountAllocation.allocation full at h
    omega
  have he : Fits bits (E + 10 + full.length) := hroom.trans halloc
  have hq3 : Fits bits (q + 3) := by
    apply PA17PackingBounds043.polynomial_fits
    have hbase := PA17A19QueryBridgeNumeric006b.base_le_cube full.length q
    have hpowers := PA17PackingBounds043.powers_le_six full.length q
    omega
  have bitmap : tableWords full.length q (treeSize q full) + q ≤ cap := by
    dsimp only [cap]
    unfold capacityWords
    rw [ite_eq_right (Nat.ne_of_gt hq)]
    omega
  exact heads_dynamic_given_actual_query full hl used cap (PSTRCountAllocation.allocation full) budget constant queryBody producer
    hwords hpcfit (original_heads_rom_fit full .query) hfoot heap (PA17A19QueryBridgeNumeric006b.bits_eight full.length q) hq rep
    hq3 bitmap (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) he hroom hbudget

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
