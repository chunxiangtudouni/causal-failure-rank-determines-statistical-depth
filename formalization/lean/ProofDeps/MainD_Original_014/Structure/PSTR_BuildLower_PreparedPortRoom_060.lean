module

public import Structure.PSTR_BuildLower_PreparedLayout_054

/-! Original common-layout consequences for each true packed/ROM port.
Margins and cached-node addresses follow the original dimensions and F8192;
the caller supplies no numeric room certificate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PreparedLayout
open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem oldCapacity_margin (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    oldCapacity q full + 5 ≤ capacity q full := by
  unfold oldCapacity capacity PA17CellLayout003.capacityWords PA17CellLayout003.workBase CompactControllerClaims.capacityWords
  rw [ite_eq_right (Nat.ne_of_gt hq)]
  omega

theorem packed_scale (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (a : Nat) (ha : a < oldCapacity q full) :
    Fits (bits q full) (a * CapacityBits.width q) :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (ha.le.trans (oldCapacity_le q full hq))) (capacity_product_fits q full hq)

theorem packed_next (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (a : Nat) (ha : a < oldCapacity q full) :
    Fits (bits q full) (a * CapacityBits.width q / bits q full + 4 + 1) := by
  have hmarg := oldCapacity_margin q full hq
  have haC : a + 5 ≤ capacity q full := by omega
  have hw : 1 ≤ CapacityBits.width q := by
    by_contra hn
    have hz : CapacityBits.width q = 0 := by omega
    have he := (CapacityBits.width_eq_zero_iff q).mp hz
    omega
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) haC
  rw [Nat.add_mul] at hm
  have hd := Nat.div_le_self (a * CapacityBits.width q) (bits q full)
  exact lt_of_le_of_lt (by omega) (capacity_product_fits q full hq)

theorem mass_fits (q : Nat) (full : List (Finset (Fin q))) :
    Fits (bits q full) (full.length + q + 1) := by
  apply PA17PackingBounds043.polynomial_fits
  have hh := Nat.pow_le_pow_right (by omega : 1 ≤ full.length + q + 2) (by decide : 1 ≤ 6)
  simp only [pow_one] at hh
  omega

theorem size_fits (q : Nat) (full : List (Finset (Fin q))) : Fits (bits q full) (t q full) :=
  lt_of_le_of_lt (prepared_indexed_size_le q full) (mass_fits q full)

theorem ord_room (q : Nat) (full : List (Finset (Fin q))) (node : (prepareNormalization q full).indexed.NodeId) :
    PA06A19PrepareBankNodeBit022.ordAddress full.length q (controlBase q full) node.val < allocated q full := by
  have hn := node.isLt
  change node.val < t q full at hn
  unfold PA06A19PrepareBankNodeBit022.ordAddress controlBase allocated
  omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PreparedLayout
