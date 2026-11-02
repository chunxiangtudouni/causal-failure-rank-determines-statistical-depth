module

public import PaperProofs.Structure.PA17_PackingBounds_043
public import PaperProofs.Structure.PSTR_QueryLayout_041

/-! Original A19 allocation/packed arithmetic bounds at one fixed existential
word factor. The implementation constants are bounded before the input;
there is no added per-instance numeric eligibility condition. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17A19QueryBridgeNumeric006b

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

theorem treeSize_bound {q : Nat} (full : List (Finset (Fin q))) :
    treeSize q full + 1 ≤ full.length + q + 2 := by
  by_cases hq : q = 0
  · simp only [treeSize, hq, ite_true]
    omega
  · simp only [treeSize, hq, ite_false]
    have ht := prepared_indexed_size_le q full
    omega

theorem base_le_cube (N q : Nat) : N + q + 2 ≤ (N + q + 2) ^ 3 := by
  have hp := Nat.pow_le_pow_right (show 1 ≤ N + q + 2 by omega) (show 1 ≤ 3 by decide)
  simpa only [pow_one] using hp

theorem table_bound {q : Nat} (full : List (Finset (Fin q))) :
    tableWords full.length q (treeSize q full) ≤ (full.length + q + 2) ^ 3 := by
  have hN : full.length + 1 ≤ full.length + q + 2 := by omega
  have hq : q + 2 ≤ full.length + q + 2 := by omega
  have ht := treeSize_bound full
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
  simpa only [tableWords, cells, pow_succ, pow_zero, Nat.one_mul] using hh

theorem capacity_bound {q : Nat} (full : List (Finset (Fin q)))
    (scratchFactor : Nat) (hs : scratchFactor ≤ 65536) :
    capacityWords scratchFactor full.length q (treeSize q full) ≤
      65538 * (full.length + q + 2) ^ 3 := by
  have ht := table_bound full
  have hb := base_le_cube full.length q
  have hq : q ≤ (full.length + q + 2) ^ 3 := (show q ≤ full.length + q + 2 by omega).trans hb
  have hsize : treeSize q full + 1 ≤ (full.length + q + 2) ^ 3 := (treeSize_bound full).trans hb
  have hscratch := Nat.mul_le_mul hs hsize
  unfold capacityWords
  split_ifs <;> omega

theorem index_bound {q : Nat} (full : List (Finset (Fin q)))
    (indexFactor : Nat) (hi : indexFactor ≤ 65536) :
    indexFactor * (full.length + q + treeSize q full + 1) ≤
      131072 * (full.length + q + 2) ^ 3 := by
  have hsize := treeSize_bound full
  have hb := base_le_cube full.length q
  have hd : full.length + q + treeSize q full + 1 ≤
      2 * (full.length + q + 2) ^ 3 := by omega
  have hm := Nat.mul_le_mul hi hd
  omega

theorem bits_eight (N q : Nat) : 8 ≤ indexWidth 32 N q := by
  have hp := PA17PackingBounds043.bits_pos N q
  unfold indexWidth at hp ⊢
  omega

theorem scalar_room {q : Nat} (full : List (Finset (Fin q)))
    (scratchFactor : Nat) (hs : scratchFactor ≤ 65536) :
    Fits (indexWidth 32 full.length q)
      (4 + capacityWords scratchFactor full.length q (treeSize q full) * CapacityBits.width q) := by
  have hc := capacity_bound full scratchFactor hs
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hm := Nat.mul_le_mul hc hw
  have hproduct : capacityWords scratchFactor full.length q (treeSize q full) * CapacityBits.width q ≤
      65538 * (full.length + q + 2) ^ 4 := by
    convert hm using 1
    ring
  apply PA17PackingBounds043.polynomial_fits
  have hp := PA17PackingBounds043.powers_le_six full.length q
  omega

theorem heap_room {q : Nat} (full : List (Finset (Fin q)))
    (scratchFactor indexFactor : Nat) (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    Fits bits (physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1)) := by
  dsimp only
  have hc := capacity_bound full scratchFactor hs
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hm := Nat.mul_le_mul hc hw
  have hproduct : capacityWords scratchFactor full.length q (treeSize q full) * CapacityBits.width q ≤
      65538 * (full.length + q + 2) ^ 4 := by
    convert hm using 1
    ring
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q
    (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q)
    (PA17PackingBounds043.bits_pos full.length q)
  have hindex := index_bound full indexFactor hi
  have hpowers := PA17PackingBounds043.powers_le_six full.length q
  apply PA17PackingBounds043.polynomial_fits
  unfold physicalHeaderWords
  omega

theorem workspace_allocated {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords indexFactor : Nat) (hq : 0 < q) (hl : LaminarSchedule full) (hi : 64 ≤ indexFactor) :
    PSTRQueryLayout.physicalWorkspace full capWords bits <
      physicalHeaderWords + packedCapacityWords q capWords bits +
        indexFactor * (full.length + q + treeSize q full + 1) := by
  have he := PSTRQueryLayout.endpoint_index_factor full capWords bits indexFactor hq hl hi
  rw [PSTRQueryLayout.endpoint_eq] at he
  omega

theorem rank_allocated {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords indexFactor : Nat) (hq : 0 < q) (hl : LaminarSchedule full) (hi : 64 ≤ indexFactor) :
    PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) +
      16 + 2 * (q + 2) ≤ physicalHeaderWords + packedCapacityWords q capWords bits +
        indexFactor * (full.length + q + treeSize q full + 1) := by
  have he := PSTRQueryLayout.endpoint_index_factor full capWords bits indexFactor hq hl hi
  unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags
    PSTRQueryLayout.goodFlags at he
  omega

end PaperProofs.Structure.LaminarTree.PA17A19QueryBridgeNumeric006b
