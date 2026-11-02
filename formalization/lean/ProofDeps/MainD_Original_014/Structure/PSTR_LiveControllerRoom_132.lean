module

public import Structure.PSTR_LiveControllerCode_129
public import Structure.PSTR_UniformQueryRoom_123

/-! Original full live-program footprint and charged call-cost arithmetic.
The step bound here must come from an actual run in the complete caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRLiveControllerRoom

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020

theorem footprint_bound (raw packed product index base : Nat)
    (hraw : raw ≤ base ^ 2) (hpacked : packed ≤ product + 1)
    (hproduct : product ≤ 65538 * base ^ 4) (hindex : index ≤ 131072 * base ^ 3)
    (h2 : base ^ 2 ≤ base ^ 6)
    (hpowers : 1 ≤ base ^ 6 ∧ base ^ 3 ≤ base ^ 6 ∧ base ^ 4 ≤ base ^ 6) :
    raw + 3 + (4 + packed + index) + 7575 ≤ 16777216 * base ^ 6 := by
  omega

theorem footprint_fit {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    Fits (wordBits full)
      ((callInput q full command).size + allocatedWords full +
        (packingCode PSTRLiveControllerCode.program).length) := by
  have hc := PA17A19QueryBridgeNumeric006b.capacity_bound full 8192 (by decide)
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hm := Nat.mul_le_mul hc hw
  have hproduct : capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q ≤
      65538 * (full.length + q + 2) ^ 4 := by
    convert hm using 1
    ring
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)
    (PA17PackingBounds043.bits_pos full.length q)
  have hi := PA17A19QueryBridgeNumeric006b.index_bound full 8192 (by decide)
  have hrom : full.length * q ≤ (full.length + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show full.length ≤ full.length + q + 2 by omega) (show q ≤ full.length + q + 2 by omega)
  have h2 : (full.length + q + 2) ^ 2 ≤ (full.length + q + 2) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hs := PA17PackingBounds043.powers_le_six full.length q
  rw [PSTRCountAllocation.input_size, PSTRLiveControllerCode.code_length]
  apply PA17PackingBounds043.polynomial_fits
  unfold allocatedWords physicalHeaderWords
  exact footprint_bound _ _ _ _ _ hrom hp hproduct hi h2 hs

theorem call_cost_bound {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (steps : Nat) (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (upper : steps ≤ PSTRUniformQuery.budget full + 124) :
    callCost q full PSTRLiveControllerCode.program command steps heap ≤ 32768 * liveWork q (treeSize q full) := by
  have budget := PSTRUniformQuery.budget_bound full
  have work := PSTRUniformQueryRoom.work_pos full
  have trace := packingDynamicTrace_length_le (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)
  unfold callCost
  rw [PSTRLiveControllerCode.code_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRLiveControllerRoom
