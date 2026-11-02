module

public import Structure.PSTR_HD_HeadsActualZero_130

/-! Literal query-body blocks are exactly unchanged when the real heads
dispatcher/tail are appended. This transports actual static CodeAt facts,
not program counter origins, dynamic execution or input-dependent code. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open RawTreePreprocessingClaims PaperProofs.Common.Native.CompactPrice

theorem heads_body_index_bound (queryBody : List PackingOp) (index : Nat) (hi : index < queryBody.length) :
    index < (uniformHeadsProgram queryBody).length := by
  rw [uniformHeadsProgram_length]
  omega

theorem heads_body_prefix_get (queryBody : List PackingOp) (index : Nat) (hi : index < queryBody.length) :
    (uniformHeadsProgram queryBody)[index]'(heads_body_index_bound queryBody index hi) = queryBody[index] := by
  change ((queryBody ++ uniformDispatch queryBody.length) ++ tailAt (queryBody.length + 8))[index]'(by
    simp only [List.length_append]; omega) = queryBody[index]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega), List.getElem_append_left hi]

theorem heads_extend_block (queryBody block : List PackingOp) (start : Nat)
    (code : PSTROuterCountCode.BlockAt queryBody start block) :
    PSTROuterCountCode.BlockAt (uniformHeadsProgram queryBody) start block := by
  refine ⟨by rw [uniformHeadsProgram_length]; have h := code.bound; omega, ?_⟩
  intro index hi
  exact (heads_body_prefix_get queryBody (start + index) (by have h := code.bound; omega)).trans (code.code index hi)

theorem heads_extend_bootstrap (queryBody : List PackingOp) (zeroStart : Nat)
    (code : PSTRUniformBootstrapCode.Contains queryBody zeroStart) :
    PSTRUniformBootstrapCode.Contains (uniformHeadsProgram queryBody) zeroStart := by
  refine ⟨by rw [uniformHeadsProgram_length]; have h := code.bound; omega, ?_⟩
  intro index hi
  exact (heads_body_prefix_get queryBody index (hi.trans_le code.bound)).trans (code.code index hi)

theorem actual_zero_heads_from_body_code (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (queryBody : List PackingOp) (zeroStart : Nat)
    (cb : PSTRUniformBootstrapCode.Contains queryBody zeroStart)
    (zs : PSTROuterCountCode.BlockAt queryBody zeroStart PSTRZeroLive.program)
    (bs : PSTROuterCountCode.BlockAt queryBody (zeroStart + 23)
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
  exact actual_zero_heads_from_code full hl used queryBody zeroStart
    (heads_extend_bootstrap queryBody zeroStart cb) (heads_extend_block queryBody _ zeroStart zs)
    (heads_extend_block queryBody _ (zeroStart + 23) bs) hlen literal heap rep

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
