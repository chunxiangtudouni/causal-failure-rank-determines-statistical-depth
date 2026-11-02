module

public import PaperProofs.Structure.PA17_Query_019
public import PaperProofs.Structure.PA17_WordBounds_023

/-! The actual complete query's code/ROM/allocation footprint fits the
original logarithmic word width. Prefix registers and accesses are separate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryFootprint025

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem powers_dominate (N q : Nat) :
    1 ≤ (N + q + 2) ^ 3 ∧ N + q + 2 ≤ (N + q + 2) ^ 3 ∧
      (N + q + 2) ^ 2 ≤ (N + q + 2) ^ 3 := by
  let base := N + q + 2
  have hb : 1 ≤ base := by dsimp [base]; omega
  have hs : base ≤ base ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left base hb
  have hc : base ^ 2 ≤ base ^ 3 := by
    change base ^ 2 ≤ base ^ 2 * base
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (base ^ 2) hb
  exact ⟨le_trans hb (hs.trans hc), hs.trans hc, hc⟩

theorem queryWork_le_cube (N q size : Nat) (hsize : size ≤ N + q + 1) :
    queryWork q size ≤ (N + q + 2) ^ 3 := by
  let base := N + q + 2
  have hq : q + 1 ≤ base := by dsimp [base]; omega
  have ht : size ≤ base := by dsimp [base]; omega
  have hh : (q + 1) * size ≤ base ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hq ht
  exact hh.trans (powers_dominate N q).2.2

theorem heapWords_le_cube (N q size : Nat) (hsize : size ≤ N + q + 1) :
    PA17QueryLayout014.heapWords N q size ≤ 36 * (N + q + 2) ^ 3 := by
  let base := N + q + 2
  have hN : N + 1 ≤ base := by dsimp [base]; omega
  have hq : q + 2 ≤ base := by dsimp [base]; omega
  have ht : size + 1 ≤ base := by dsimp [base]; omega
  have htable : (N + 1) * (q + 2) * (size + 1) ≤ base ^ 3 := by
    calc
      _ ≤ (base * base) * base := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
      _ = base ^ 3 := by ring
  have hpow := powers_dominate N q
  change 1 ≤ base ^ 3 ∧ base ≤ base ^ 3 ∧ base ^ 2 ≤ base ^ 3 at hpow
  dsimp [PA17QueryLayout014.heapWords, PA17QueryLayout014.capacityWords,
    PA17CellLayout003.capacityWords, PA17CellLayout003.workBase, tableWords, cells,
    PA17QueryLayout014.indexWords]
  change (N + 1) * (q + 2) * (size + 1) + 2 * (size + 1) + (6 * size + N + 2 * q + 24) ≤ 36 * base ^ 3
  nlinarith

theorem queryROM_size (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    (queryROM q full stage used).size = (givenTreeROM q full).size + q + 1 := by
  simp only [queryROM, PhysicalROM.size, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]
  omega

theorem queryROM_size_le_cube (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Nat) (used : Finset (Fin q)) :
    (queryROM q full stage used).size ≤ 10 * (full.length + q + 2) ^ 3 := by
  let N := full.length
  let size := (prepareNormalization q full).indexed.nodes.size
  let base := N + q + 2
  have ht : size ≤ N + q + 1 := prepared_indexed_size_le q full
  have hN : N ≤ base := by dsimp [base]; omega
  have hq' : q ≤ base := by dsimp [base]; omega
  have ht' : size ≤ base := by dsimp [base]; omega
  have hNq : N * q ≤ base ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hN hq'
  have htq : size * q ≤ base ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul ht' hq'
  have hp := powers_dominate N q
  change 1 ≤ base ^ 3 ∧ base ≤ base ^ 3 ∧ base ^ 2 ≤ base ^ 3 at hp
  rw [queryROM_size, PhysicalROM.size, RawTreeSerialization.givenTreeROM_input_length,
    RawTreeSerialization.givenTreeROM_internal_length, RawTreeSerialization.givenTreeROM_children_length q full hq hlaminar]
  change 3 + N * q + size * q + 2 * size + (size - 1) + q + 1 ≤ 10 * base ^ 3
  have hs : size - 1 ≤ size := Nat.sub_le _ _
  nlinarith

theorem query_code_length_le (N q size : Nat) (hsize : 0 < size) :
    (haltingWords (PA17Query019.program N q size)).length ≤ 16384 * queryWork q size := by
  have ht := PA17Query019.totalQueryCost_le N q size hsize
  dsimp only [totalQueryCost] at ht
  omega

theorem prepared_query_footprint (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1))
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (queryROM q full stage.val used).size + PA17QueryLayout014.heapWords full.length q size +
      (haltingWords (PA17Query019.program full.length q size)).length ≤ 65536 * (full.length + q + 2) ^ 3 := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have ht : size ≤ full.length + q + 1 := prepared_indexed_size_le q full
  have hh := heapWords_le_cube full.length q size ht
  have hr := queryROM_size_le_cube q full hq hlaminar stage.val used
  have hc := query_code_length_le full.length q size hsize
  have hw := queryWork_le_cube full.length q size ht
  nlinarith

theorem prepared_query_footprint_fits (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1))
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    Fits (indexWidth 32 full.length q)
      ((queryROM q full stage.val used).size + PA17QueryLayout014.heapWords full.length q size +
        (haltingWords (PA17Query019.program full.length q size)).length) :=
  PA17WordBounds023.cubic_fits full.length q _ (prepared_query_footprint q full hq hlaminar stage used)

end PaperProofs.Structure.LaminarTree.PA17QueryFootprint025
