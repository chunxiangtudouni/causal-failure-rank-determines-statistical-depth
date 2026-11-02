module

public import Structure.PSTR_BuildLower_SourceFacts_046
public import Structure.PSTR_BuildLower_ViewStep_045
public import Structure.PSTR_BuildLower_BuilderRoom_039
public import Structure.PA06_A19Prepare_ControlBank017_Geometry

/-! Internal room parameters for the common F8192/w32 prepare ABI. The
original finite source domain, ordinary rebasing, actual control bank and new
packed capacity satisfy the component inequalities without caller room fields. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PreparedLayout
open IndexedRAM IndexedClosureRAM AlgorithmClaims

abbrev t (q : Nat) (full : List (Finset (Fin q))) : Nat := SourceFacts.size q full
abbrev bits (q : Nat) (full : List (Finset (Fin q))) : Nat := indexWidth 32 full.length q
def oldCapacity (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  PA17CellLayout003.capacityWords full.length q (t q full)
def capacity (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  CompactControllerClaims.capacityWords 8192 full.length q (t q full)
def packed (q : Nat) (full : List (Finset (Fin q))) : Nat := packedCapacityWords q (capacity q full) (bits q full)
def indexBase (q : Nat) (full : List (Finset (Fin q))) : Nat := 4 + packed q full
def indexWords (q : Nat) (full : List (Finset (Fin q))) : Nat := 6 * t q full + full.length + 2 * q + 31
def controlBase (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  4 + packed q full + 4096 * (full.length + q + 1 + t q full)
def allocated (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  4 + packed q full + 8192 * (full.length + q + 1 + t q full)

theorem oldCapacity_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    oldCapacity q full ≤ capacity q full :=
  PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q (t q full) hq

theorem source_domain (q : Nat) (full : List (Finset (Fin q))) :
    PA17QueryLayout014.heapWords full.length q (t q full) ≤ oldCapacity q full + indexWords q full := by
  change PA17CellLayout003.capacityWords full.length q (t q full) +
      (6 * t q full + full.length + 2 * q + 24) ≤ oldCapacity q full + indexWords q full
  unfold oldCapacity indexWords
  omega

theorem ordinary_before_control (q : Nat) (full : List (Finset (Fin q))) :
    indexBase q full + indexWords q full ≤ controlBase q full := by
  unfold indexBase indexWords controlBase
  omega

theorem packed_lookahead_before_end (q : Nat) (full : List (Finset (Fin q))) :
    4 + packed q full + 1 ≤ indexBase q full + indexWords q full := by
  unfold indexBase indexWords
  omega

theorem allocation_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (bits q full) (allocated q full) := by
  have ht : CompactControllerClaims.treeSize q full = t q full := by
    simp only [CompactControllerClaims.treeSize, Nat.ne_of_gt hq, ite_false]
  have hh := PA06A19PrepareControlBank017.actual_allocation_fits full
  simpa only [ht, allocated, packed, capacity, bits,
    PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
    PA06A19PrepareControlBank017.mass] using hh

theorem bank512_room (q : Nat) (full : List (Finset (Fin q))) :
    controlBase q full + 512 < allocated q full := by
  unfold controlBase allocated
  omega

theorem bank_offset_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (offset : Nat) (ho : offset ≤ 512) :
    Fits (bits q full) (controlBase q full + offset) :=
  (lt_of_le_of_lt (Nat.add_le_add_left ho _) (bank512_room q full)).trans (allocation_fits q full hq)

theorem ordinary_end_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (bits q full) (indexBase q full + indexWords q full) :=
  lt_of_le_of_lt (ordinary_before_control q full) (bank_offset_fits q full hq 0 (by decide))

theorem capacity_product_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (bits q full) (capacity q full * CapacityBits.width q) := by
  have ht : CompactControllerClaims.treeSize q full = t q full := by
    simp only [CompactControllerClaims.treeSize, Nat.ne_of_gt hq, ite_false]
  have hc := PA06A19PrepareControlBank017.common_capacity_bound full
  rw [ht] at hc
  have hp : capacity q full * CapacityBits.width q ≤ 8194 * (full.length + q + 2) ^ 4 := by
    calc
      _ ≤ (8194 * (full.length + q + 2) ^ 3) * (full.length + q + 2) :=
        Nat.mul_le_mul hc (PA17PackingBounds043.width_le_base full.length q)
      _ = _ := by ring
  apply PA17PackingBounds043.polynomial_fits
  have hh := PA17PackingBounds043.powers_le_six full.length q
  omega

theorem width_room (q : Nat) (full : List (Finset (Fin q))) : CapacityBits.width q ≤ bits q full :=
  PA17PackingBounds043.width_le_bits full.length q

theorem bits_room (q : Nat) (full : List (Finset (Fin q))) : 32 ≤ bits q full :=
  CounterInit.selected_width_room full.length q

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PreparedLayout
