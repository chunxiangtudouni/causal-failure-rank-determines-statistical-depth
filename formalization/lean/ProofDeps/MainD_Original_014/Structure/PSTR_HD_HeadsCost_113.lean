module

public import Structure.PSTR_HD_HeadsOriginalInitialSafe_111

/-! Actual charged trace and original callCost arithmetic for the ONE fixed
uniform program. This converts a real global clock bound into headWork; it
does not assert such a run or manufacture an internal query producer. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open PaperProofs.Common.Native.CompactPrice

theorem original_liveWork_one_le {q : Nat} (full : List (Finset (Fin q))) :
    1 ≤ liveWork q (treeSize q full) := by
  by_cases hq : q = 0
  · simp [liveWork, hq]
  · have hqpos : 0 < q := by omega
    have ht := IndexedRawClosureRAM.prepared_q_le_nodes q full hqpos
    simp only [liveWork, treeSize, hq, ↓reduceIte, queryWork]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos q) (hqpos.trans_le ht))

theorem original_headWork_one_le {q : Nat} (full : List (Finset (Fin q))) :
    1 ≤ headWork q full := by
  have hw := original_liveWork_one_le full
  unfold headWork
  exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos full.length) (by omega))

theorem uniform_heads_code_length (queryBody : List PackingOp) :
    (packingCode (uniformHeadsProgram queryBody)).length = 5 * queryBody.length + 600 := by
  rw [packingCode_length, uniformHeadsProgram_length]
  omega

theorem actual_heads_callCost_le {bits q : Nat} (full : List (Finset (Fin q)))
    (queryBody : List PackingOp) (heap : BitVec bits → BitVec bits) (steps budget constant : Nat)
    (hsteps : steps ≤ (full.length + 1) * (budget + 88))
    (hbudget : budget ≤ constant * liveWork q (treeSize q full)) :
    callCost q full (uniformHeadsProgram queryBody) .query steps heap ≤
      (12 * constant + 5 * queryBody.length + 1665) * headWork q full := by
  have hwork := original_liveWork_one_le full
  have hhead := original_headWork_one_le full
  have hclock : steps ≤ (constant + 88) * headWork q full := by
    calc
      steps ≤ (full.length + 1) * (budget + 88) := hsteps
      _ ≤ (full.length + 1) * ((constant + 88) * liveWork q (treeSize q full)) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ = (constant + 88) * headWork q full := by unfold headWork; ring
  have htrace := packingDynamicTrace_length_le (callInput q full .query)
    (uniformHeadsProgram queryBody) steps (packingInitial heap)
  have hfixed : 5 * queryBody.length + 609 ≤ (5 * queryBody.length + 609) * headWork q full := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (5 * queryBody.length + 609) hhead
  have hcharged := Nat.mul_le_mul_left 12 hclock
  unfold callCost
  rw [uniform_heads_code_length]
  nlinarith

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
