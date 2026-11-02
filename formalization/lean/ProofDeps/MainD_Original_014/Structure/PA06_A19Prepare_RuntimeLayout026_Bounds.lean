module

public import Structure.PA06_A19Prepare_RuntimeLayout026
public import PaperProofs.Structure.PA17_PackedTemplates_046e
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: original-data arithmetic room for the fixed 026
instructions. In particular the numerator BEFORE subtraction/division fits;
physical allocation Fits alone is never used as a substitute for C*width. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

theorem bits_le_linear (N q : Nat) : indexWidth 32 N q ≤ 32 * (N + q + 2) := by
  have hh : Nat.clog 2 (N + q + 2) ≤ N + q + 2 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  exact Nat.mul_le_mul_left 32 hh

/-- The actual addition executed before subtract1 and divide, at the SAME
wordFactor32 and the ORIGINAL commonF8192 capacity. -/
theorem actual_product_plus_bits_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q)
      (capacityExpr full.length q (treeSize q full) * CapacityBits.width q + indexWidth 32 full.length q) := by
  rw [capacityExpr_eq _ _ _ hq]
  have hc := PA06A19PrepareControlBank017.common_capacity_bound full
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hproduct : capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q ≤
      8194 * (full.length + q + 2) ^ 4 := by
    calc
      _ ≤ (8194 * (full.length + q + 2) ^ 3) * (full.length + q + 2) := Nat.mul_le_mul hc hw
      _ = 8194 * (full.length + q + 2) ^ 4 := by ring
  have hb := bits_le_linear full.length q
  have hp := PA17PackingBounds043.powers_le_six full.length q
  have hbase : full.length + q + 2 ≤ (full.length + q + 2) ^ 6 := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ full.length + q + 2 by omega) (show 1 ≤ 6 by decide)
    simpa only [pow_one] using hh
  apply PA17PackingBounds043.polynomial_fits
  omega

theorem actual_capacity_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q) (capacityExpr full.length q (treeSize q full)) := by
  have hh := actual_product_plus_bits_fits q full hq
  have hp := PA17PackedTemplates046.width_pos q hq
  exact ((Nat.le_mul_of_pos_right _ hp).trans (Nat.le_add_right _ _)).trans_lt hh

theorem actual_product_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q) (capacityExpr full.length q (treeSize q full) * CapacityBits.width q) :=
  (Nat.le_add_right _ _).trans_lt (actual_product_plus_bits_fits q full hq)

theorem actual_numerator_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q)
      (capacityExpr full.length q (treeSize q full) * CapacityBits.width q + indexWidth 32 full.length q - 1) :=
  (Nat.sub_le _ _).trans_lt (actual_product_plus_bits_fits q full hq)

theorem actual_packed_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q)
      (packedExpr (capacityExpr full.length q (treeSize q full)) (CapacityBits.width q) (indexWidth 32 full.length q)) :=
  (Nat.div_le_self _ _).trans_lt (actual_numerator_fits q full hq)

/-- The runtime tree-size load is inside the genuine source prefix and
therefore inside the unchanged original commonF8192 allocation. -/
theorem actual_tree_source_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q) (20 + 4 * (full.length + q + 1)) := by
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  have hs : 20 + 4 * (full.length + q + 1) < PA06A19PrepareControlBank017.cacheLength full.length q := by
    unfold PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass
    omega
  have hd := PA06A19PrepareControlBank017.source_target_disjoint full.length q t P hq
  have hr := PA06A19PrepareControlBank017.actual_cache_room full hq
  have ha : PA06A19PrepareControlBank017.cacheBase full.length q t P <
      PA06A19PrepareControlBank017.allocation full.length q t P := by
    exact (Nat.le_add_right _ _).trans_lt hr.1
  exact (hs.trans_le hd).trans (ha.trans (PA06A19PrepareControlBank017.actual_allocation_fits full))

theorem actual_bank_field_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (offset : Nat) (hoffset : offset ≤ 6) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    Fits (indexWidth 32 full.length q) (PA06A19PrepareControlBank017.controlBase full.length q t P + offset) := by
  dsimp only
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  have hd := PA06A19PrepareControlBank017.controls_cache_disjoint full.length q t P offset (by omega)
  have hr := PA06A19PrepareControlBank017.actual_cache_room full hq
  have ha : PA06A19PrepareControlBank017.cacheBase full.length q t P <
      PA06A19PrepareControlBank017.allocation full.length q t P :=
    (Nat.le_add_right _ _).trans_lt hr.1
  exact hd.trans (ha.trans (PA06A19PrepareControlBank017.actual_allocation_fits full))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
