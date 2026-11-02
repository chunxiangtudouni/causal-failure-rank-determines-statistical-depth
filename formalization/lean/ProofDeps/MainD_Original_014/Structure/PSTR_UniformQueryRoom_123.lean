module

public import Structure.PSTR_UniformQuery_122

/-! Whole original ROM/heap/6860-word code footprint, including q=0. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformQueryRoom

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020

theorem work_pos {q : Nat} (full : List (Finset (Fin q))) :
    1 ≤ liveWork q (treeSize q full) := by
  by_cases hq : q = 0
  · simp only [liveWork, hq, ite_true]
    exact Nat.le_refl _
  · have ht := PSTRWidthOriginal.positive_tree_size full (Nat.pos_of_ne_zero hq)
    simp only [liveWork, hq, ite_false, queryWork]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) ht)

theorem footprint_bound (raw packed product index base : Nat)
    (hraw : raw ≤ base ^ 2) (hpacked : packed ≤ product + 1)
    (hproduct : product ≤ 65538 * base ^ 4) (hindex : index ≤ 131072 * base ^ 3)
    (h2 : base ^ 2 ≤ base ^ 6)
    (hpowers : 1 ≤ base ^ 6 ∧ base ^ 3 ≤ base ^ 6 ∧ base ^ 4 ≤ base ^ 6) :
    raw + 3 + (4 + packed + index) + 6860 ≤ 16777216 * base ^ 6 := by
  omega

theorem footprint_fit {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    Fits (wordBits full)
      ((callInput q full command).size + allocatedWords full +
        (packingCode PSTRUniformQueryCode.program).length) := by
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
  rw [PSTRCountAllocation.input_size, PSTRUniformQueryCode.code_length]
  apply PA17PackingBounds043.polynomial_fits
  unfold allocatedWords physicalHeaderWords
  exact footprint_bound _ _ _ _ _ hrom hp hproduct hi h2 hs

end PaperProofs.Structure.LaminarTree.PSTRUniformQueryRoom
