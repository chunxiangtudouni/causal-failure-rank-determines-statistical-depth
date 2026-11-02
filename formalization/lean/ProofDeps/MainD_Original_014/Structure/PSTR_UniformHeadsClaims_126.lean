module

public import Structure.PSTR_UniformHeadsProducer_125

/-! Actual ALL-q whole heads extraction from original prepared HeapRep.
The same one1371-op query is reused at every scanned stage. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRHeadsRuntime
open PaperProofs.Common.Native.CompactPrice

theorem actual_heads {q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) ⟨0, used, false⟩ heap) :
    ∃ steps ≤ (full.length + 1) * (PSTRUniformQuery.budget full + 101),
      DynamicRunCorrect (allocatedWords full) (callInput q full .query) program steps heap ∧
      callCost q full program .query steps heap ≤ 30000 * headWork q full ∧
      (let after := packingRun (callInput q full .query) program steps (packingInitial heap);
        HeapRepresents q full (capacity full) ⟨full.length, used, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords q full used).length ≤ allocatedWords full ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords q full used).length = headWords q full used) := by
  by_cases hq : q = 0
  · subst q
    have back : PSTROuterCountCode.BlockAt PSTRUniformQueryCode.program (1345 + 23)
        (PSTRCountControl.backBlock PSTRUniformQueryCode.program.length) := by
      rw [PSTRUniformQueryCode.program_length]
      exact PSTRUniformQueryCode.zero_return_in _ PSTRUniformQueryCode.self_contains
    obtain ⟨steps, upper, dynamic, cost, output⟩ := actual_zero_heads_from_body_code full hl used
      PSTRUniformQueryCode.program 1345
      (PSTRUniformQueryCode.bootstrap_in _ PSTRUniformQueryCode.self_contains)
      (PSTRUniformQueryCode.zero_in _ PSTRUniformQueryCode.self_contains) back body_length body_literal heap rep
    refine ⟨steps, upper.trans (Nat.mul_le_mul_left _ (by omega)), dynamic, ?_, output⟩
    have hc : 5 * PSTRUniformQueryCode.program.length + 2193 ≤ 30000 := by
      rw [PSTRUniformQueryCode.program_length]
      decide
    exact cost.trans (Nat.mul_le_mul_right _ hc)
  · obtain ⟨steps, upper, dynamic, cost, output⟩ := original_positive_heads_given_actual_query full
      (Nat.pos_of_ne_zero hq) hl used PSTRUniformQueryCode.program (PSTRUniformQuery.budget full) 1790
      (actual_positive_producer full (Nat.pos_of_ne_zero hq) hl used) body_length body_literal
      (PSTRUniformQuery.budget_bound full) heap rep
    refine ⟨steps, upper.trans (Nat.mul_le_mul_left _ (by omega)), dynamic, ?_, output⟩
    rw [PSTRUniformQueryCode.program_length] at cost
    exact cost

end PaperProofs.Structure.LaminarTree.PSTRUniformHeads
