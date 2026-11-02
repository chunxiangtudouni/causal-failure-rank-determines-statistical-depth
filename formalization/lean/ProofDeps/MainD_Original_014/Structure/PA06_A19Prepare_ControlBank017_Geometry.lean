module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.PA17_PackingBounds_043
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000

/-! Private uncompiled concrete common-F8192 prepare bank geometry.
No new allocation is used. These lemmas do not create runtime headers or
perform relocation; the actual copy kernel is in ControlBank017. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

def mass (N q : Nat) : Nat := N + q + 1
def dimensions (N q t : Nat) : Nat := mass N q + t
def controlBase (N q t packed : Nat) : Nat := 4 + packed + 4096 * dimensions N q t
def cacheBase (N q t packed : Nat) : Nat := controlBase N q t packed + 512
def cacheAllowance (N q : Nat) : Nat := 16 + 8 * mass N q + 8192
def cacheLength (N q : Nat) : Nat := 16 + 5 + 5 * mass N q
def allocation (N q t packed : Nat) : Nat := 4 + packed + 8192 * dimensions N q t

theorem geometry (N q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    512 + cacheAllowance N q < 4096 * dimensions N q t := by
  unfold cacheAllowance dimensions mass
  omega

theorem cacheLength_le_allowance (N q : Nat) : cacheLength N q ≤ cacheAllowance N q := by
  unfold cacheLength cacheAllowance
  omega

theorem cache_end_room (N q t packed : Nat) (hq : 0 < q) (ht : 0 < t) :
    cacheBase N q t packed + cacheAllowance N q < allocation N q t packed := by
  have h := geometry N q t hq ht
  unfold cacheBase controlBase allocation
  omega

theorem source_target_disjoint (N q t packed : Nat) (_hq : 0 < q) :
    cacheLength N q ≤ cacheBase N q t packed := by
  unfold cacheLength cacheBase controlBase dimensions mass
  omega

theorem packed_control_disjoint (N q t packed address : Nat)
    (haddress : address < 4 + packed) : address < controlBase N q t packed := by
  unfold controlBase
  omega

theorem controls_cache_disjoint (N q t packed offset : Nat) (hoffset : offset < 512) :
    controlBase N q t packed + offset < cacheBase N q t packed := by
  unfold cacheBase
  omega

theorem loop_virtual_slots_disjoint (N q t packed virtual temp : Nat)
    (hv : virtual < 7) (ht : 64 ≤ temp) :
    controlBase N q t packed + 32 + virtual < controlBase N q t packed + temp := by
  omega

theorem treeSize_pos {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) :
    0 < treeSize q full := by
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp := root.isLt
  simp only [treeSize, Nat.ne_of_gt hq, ite_false]
  omega

theorem treeSize_bound {q : Nat} (full : List (Finset (Fin q))) :
    treeSize q full + 1 ≤ full.length + q + 2 := by
  by_cases hq : q = 0
  · simp only [treeSize, hq, ite_true]
    omega
  · simp only [treeSize, hq, ite_false]
    have ht := prepared_indexed_size_le q full
    omega

theorem table_bound {q : Nat} (full : List (Finset (Fin q))) :
    tableWords full.length q (treeSize q full) ≤ (full.length + q + 2) ^ 3 := by
  have hN : full.length + 1 ≤ full.length + q + 2 := by omega
  have hq : q + 2 ≤ full.length + q + 2 := by omega
  have ht := treeSize_bound full
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
  simpa only [tableWords, cells, pow_succ, pow_zero, Nat.one_mul] using hh

theorem common_capacity_bound {q : Nat} (full : List (Finset (Fin q))) :
    capacityWords 8192 full.length q (treeSize q full) ≤
      8194 * (full.length + q + 2) ^ 3 := by
  have ht := table_bound full
  have hb : full.length + q + 2 ≤ (full.length + q + 2) ^ 3 := by
    have hp := Nat.pow_le_pow_right (show 1 ≤ full.length + q + 2 by omega) (show 1 ≤ 3 by decide)
    simpa only [pow_one] using hp
  have hq : q ≤ (full.length + q + 2) ^ 3 := (show q ≤ full.length + q + 2 by omega).trans hb
  have hs : treeSize q full + 1 ≤ (full.length + q + 2) ^ 3 := (treeSize_bound full).trans hb
  unfold capacityWords
  split_ifs <;> omega

/-- Word room for the SAME actual A19 allocation, not an old unpacked heap. -/
theorem actual_allocation_fits {q : Nat} (full : List (Finset (Fin q))) :
    Fits (indexWidth 32 full.length q)
      (allocation full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q))) := by
  have hc := common_capacity_bound full
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hm := Nat.mul_le_mul hc hw
  have hproduct : capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q ≤
      8194 * (full.length + q + 2) ^ 4 := by
    convert hm using 1
    ring
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)
    (PA17PackingBounds043.bits_pos full.length q)
  have ht := treeSize_bound full
  have hb : full.length + q + 2 ≤ (full.length + q + 2) ^ 3 := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ full.length + q + 2 by omega) (show 1 ≤ 3 by decide)
    simpa only [pow_one] using hh
  have hpowers := PA17PackingBounds043.powers_le_six full.length q
  apply PA17PackingBounds043.polynomial_fits
  unfold allocation dimensions mass
  omega

/-- Every actual control/cache address, including lookahead and end pointer,
is in the original allocation and the common wordFactor32. -/
theorem actual_cache_room {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    cacheBase full.length q t P + cacheAllowance full.length q < allocation full.length q t P ∧
      Fits (indexWidth 32 full.length q) (cacheBase full.length q t P + cacheAllowance full.length q) := by
  dsimp only
  have h := cache_end_room full.length q (treeSize q full)
    (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q)) hq (treeSize_pos full hq)
  exact ⟨h, h.trans (actual_allocation_fits full)⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareControlBank017
