module

public import Structure.PA06_A19Prepare_InitialUsed037_BodySafety
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate original-data bounds for every j<q iteration. None of these
lemmas takes a packed-access certificate or a final loop result as input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM

def usedPointer (N q t j : Nat) : Nat := tableWords N q t + j
def romCursor (N q j : Nat) : Nat := 2 + N * q + j

theorem pointer_lt_capacity (N q t j : Nat) (hq : 0 < q) (hj : j < q) :
    usedPointer N q t j < capacityWords 8192 N q t := by
  unfold usedPointer capacityWords
  rw [ite_eq_right (Nat.ne_of_gt hq)]
  omega

theorem pointer_next_le_capacity (N q t j : Nat) (hq : 0 < q) (hj : j < q) :
    usedPointer N q t j + 1 ≤ capacityWords 8192 N q t := by
  have hh := pointer_lt_capacity N q t j hq hj
  omega

theorem cursor_next_le_capacity (N q t j : Nat) (hq : 0 < q) (hj : j < q) :
    romCursor N q j + 1 ≤ capacityWords 8192 N q t := by
  have hh := raw_end_le_capacity N q t hq
  unfold romCursor
  omega

theorem actual_pointer_product_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (j : Nat) (hj : j < q) :
    Fits (indexWidth 32 full.length q) (usedPointer full.length q (treeSize q full) j * CapacityBits.width q) := by
  have ha := pointer_lt_capacity full.length q (treeSize q full) j hq hj
  have hh := PA06A19PrepareRuntimeLayout026.actual_product_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hh
  exact (Nat.mul_le_mul_right _ ha.le).trans_lt hh

theorem actual_pointer_next_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (j : Nat) (hj : j < q) :
    Fits (indexWidth 32 full.length q) (usedPointer full.length q (treeSize q full) j + 1) := by
  have hh := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hh
  exact (pointer_next_le_capacity full.length q (treeSize q full) j hq hj).trans_lt hh

theorem actual_cursor_next_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (j : Nat) (hj : j < q) : Fits (indexWidth 32 full.length q) (romCursor full.length q j + 1) := by
  have hh := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hh
  exact (cursor_next_le_capacity full.length q (treeSize q full) j hq hj).trans_lt hh

theorem actual_physical_next_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (j : Nat) (hj : j < q) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let a := usedPointer full.length q t j
    let next := a * CapacityBits.width q / bits + 4 + 1
    Fits bits next ∧ next < PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
  dsimp only
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let a := usedPointer full.length q t j
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  have ha : a < C := pointer_lt_capacity full.length q t j hq hj
  have hw := PA17PackedTemplates046.width_pos q hq
  have hb := PA17PackingBounds043.bits_pos full.length q
  have hd : a * CapacityBits.width q / bits < P := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    exact (Nat.mul_lt_mul_of_pos_right ha hw).trans_le (packedCapacityWords_mul_bits q C hb)
  have hbefore : a * CapacityBits.width q / bits + 4 + 1 ≤ CB + pointerSlot := by
    dsimp only [CB, pointerSlot, PA06A19PrepareControlBank017.controlBase]
    omega
  have hr := actual_control_room q full hq pointerSlot (by decide)
  exact ⟨hbefore.trans_lt hr.2, hbefore.trans_lt hr.1⟩

theorem actual_control_after_lookahead (q : Nat) (full : List (Finset (Fin q))) (slot : Nat) :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    4 + P + 1 ≤ PA06A19PrepareControlBank017.controlBase full.length q t P + slot := by
  dsimp only [PA06A19PrepareControlBank017.controlBase, PA06A19PrepareControlBank017.dimensions,
    PA06A19PrepareControlBank017.mass]
  omega

theorem actual_cursor_read_lt (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (j : Nat) (hj : j < q) : romCursor full.length q j < ((controllerInput q full used).words .input).length := by
  change 2 + full.length * q + j < (controllerInput q full used).input.length
  exact PA06A19PrepareFinalHeader033InitialUsedROM.used_address_lt q full used ⟨j, hj⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
