module
public import PaperProofs.Structure.PA17_WordBounds_023
public import PaperProofs.Structure.PA17_QueryFootprint_025
public import PaperProofs.Structure.PackedCapacityRAM

/-! Pure literal/address bounds for the physical translator at word factor32.
Physical packed allocation alone does not imply Fits of C or C*width(q);
those necessary bounds are proved here from original polynomial layouts. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17PackingBounds043

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem polynomial_fits (N q value : Nat) (hvalue : value ≤ 16777216 * (N + q + 2) ^ 6) :
    Fits (indexWidth 32 N q) value := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hp : 16777216 < base ^ 26 :=
    lt_of_lt_of_le (by decide : 16777216 < 2 ^ 26) (Nat.pow_le_pow_left hb 26)
  have hpos : 0 < base ^ 6 := pow_pos (by omega) _
  calc
    value ≤ 16777216 * base ^ 6 := hvalue
    _ < base ^ 6 * base ^ 26 := by nlinarith
    _ = base ^ 32 := by rw [← pow_add]

theorem width_le_base (N q : Nat) : CapacityBits.width q ≤ N + q + 2 := by
  have hh : CapacityBits.width q ≤ q + 1 := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  omega

theorem width_le_bits (N q : Nat) : CapacityBits.width q ≤ indexWidth 32 N q := by
  have hh : CapacityBits.width q ≤ Nat.clog 2 (N + q + 2) := Nat.clog_mono_right 2 (by omega)
  unfold indexWidth
  omega

theorem bits_pos (N q : Nat) : 0 < indexWidth 32 N q := by
  have hs := PA17WordBounds023.small_word_fit N q
  change 8 < 2 ^ (indexWidth 32 N q) at hs
  by_contra h
  have he : indexWidth 32 N q = 0 := by omega
  rw [he] at hs
  norm_num at hs

theorem powers_le_six (N q : Nat) :
    1 ≤ (N + q + 2) ^ 6 ∧ (N + q + 2) ^ 3 ≤ (N + q + 2) ^ 6 ∧
      (N + q + 2) ^ 4 ≤ (N + q + 2) ^ 6 :=
  ⟨Nat.one_le_pow _ _ (by omega), Nat.pow_le_pow_right (by omega) (by decide),
    Nat.pow_le_pow_right (by omega) (by decide)⟩

theorem capacityProduct_le (N q capWords : Nat) (hc : capWords ≤ 36 * (N + q + 2) ^ 3) :
    capWords * CapacityBits.width q ≤ 36 * (N + q + 2) ^ 4 := by
  calc
    _ ≤ (36 * (N + q + 2) ^ 3) * (N + q + 2) := Nat.mul_le_mul hc (width_le_base N q)
    _ = _ := by ring

theorem capacity_fits (N q capWords : Nat) (hc : capWords ≤ 36 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q) capWords := by
  apply polynomial_fits
  have hp := powers_le_six N q
  omega

theorem capacityProduct_fits (N q capWords : Nat) (hc : capWords ≤ 36 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q) (capWords * CapacityBits.width q) := by
  apply polynomial_fits
  have hh := capacityProduct_le N q capWords hc
  have hp := powers_le_six N q
  omega

theorem packedCapacityWords_le_product (q capWords bits : Nat) (hb : 0 < bits) :
    packedCapacityWords q capWords bits ≤ capWords * CapacityBits.width q + 1 := by
  have hm : capWords * CapacityBits.width q ≤ (capWords * CapacityBits.width q) * bits :=
    Nat.le_mul_of_pos_right _ hb
  have hstrict : (capWords * CapacityBits.width q + bits - 1) / bits <
      capWords * CapacityBits.width q + 1 := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    calc
      _ < capWords * CapacityBits.width q + bits := Nat.sub_lt (by omega) (by decide)
      _ ≤ (capWords * CapacityBits.width q) * bits + bits := Nat.add_le_add_right hm bits
      _ = _ := by ring
  exact hstrict.le

theorem physicalHeap_fits (N q capWords oldIndexWords : Nat)
    (hc : capWords ≤ 36 * (N + q + 2) ^ 3) (hi : oldIndexWords ≤ 36 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q)
      (packedCapacityWords q capWords (indexWidth 32 N q) + oldIndexWords + 7) := by
  apply polynomial_fits
  have hp := packedCapacityWords_le_product q capWords (indexWidth 32 N q) (bits_pos N q)
  have hprod := capacityProduct_le N q capWords hc
  have hpowers := powers_le_six N q
  omega

theorem scalarMask_fits (N q : Nat) : Fits (indexWidth 32 N q) (2 ^ CapacityBits.width q - 1) := by
  have hp : 0 < 2 ^ CapacityBits.width q := pow_pos (by decide) _
  exact (Nat.sub_lt hp (by decide : 0 < 1)).trans_le
    (Nat.pow_le_pow_right (by decide) (width_le_bits N q))

theorem fullCapacity_le (q : Nat) (full : List (Finset (Fin q))) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PA17QueryLayout014.capacityWords full.length q size ≤ 36 * (full.length + q + 2) ^ 3 := by
  intro size
  exact (Nat.le_add_right _ _).trans
    (PA17QueryFootprint025.heapWords_le_cube full.length q size (prepared_indexed_size_le q full))

end PaperProofs.Structure.LaminarTree.PA17PackingBounds043
