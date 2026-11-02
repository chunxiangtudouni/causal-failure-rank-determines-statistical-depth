module

public import Structure.PA06_A19Prepare_ZeroHeader080_Safe

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED original common32/8192 bounds, including N=0 and q=0. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

abbrev wordBits (N : Nat) : Nat := indexWidth 32 N 0
def wordLimit (N : Nat) : Nat := 2 ^ wordBits N - 1
abbrev allocation (N : Nat) : Nat := PA06A19PrepareRuntimeHeader019.heapWords N 0 0

theorem bits_ge32 (N : Nat) : 32 ≤ wordBits N := by
  have hp : 0 < Nat.clog 2 (N + 2) := Nat.clog_pos (by decide) (by omega)
  simp only [wordBits, indexWidth, Nat.add_zero]
  omega

theorem limit_fits (N : Nat) : Fits (wordBits N) (wordLimit N) := by
  have hp : 0 < 2 ^ wordBits N := pow_pos (by decide) _
  unfold Fits wordLimit
  omega

theorem small_le_limit (N : Nat) : 69 ≤ wordLimit N := by
  have hp : 2 ^ 32 ≤ 2 ^ wordBits N := Nat.pow_le_pow_right (by decide) (bits_ge32 N)
  have small : 70 ≤ 2 ^ 32 := by decide
  unfold wordLimit
  omega

theorem input_le_limit (N : Nat) : N + 1 ≤ wordLimit N := by
  have hp : N + 2 ≤ 2 ^ Nat.clog 2 (N + 2) := Nat.le_pow_clog (by decide) (N + 2)
  have hl : Nat.clog 2 (N + 2) ≤ wordBits N := by
    simp only [wordBits, indexWidth, Nat.add_zero]
    omega
  have powers : 2 ^ Nat.clog 2 (N + 2) ≤ 2 ^ wordBits N := Nat.pow_le_pow_right (by decide) hl
  unfold wordLimit
  omega

theorem bits_le_limit (N : Nat) : wordBits N ≤ wordLimit N := by
  have hp : wordBits N < 2 ^ wordBits N := Nat.lt_pow_self (by decide)
  unfold wordLimit
  omega

theorem zero_packed_words (bits : Nat) (hb : 0 < bits) : packedCapacityWords 0 0 bits = 0 := by
  simp only [packedCapacityWords, Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

theorem allocation_eq (N : Nat) : allocation N = 4 + 8192 * (N + 1) := by
  change 4 + packedCapacityWords 0 0 (wordBits N) + 8192 * (N + 0 + 0 + 1) = _
  rw [zero_packed_words _ (PA17PackingBounds043.bits_pos N 0)]

theorem original_allocation (full : List (Finset (Fin 0))) :
    allocation full.length = physicalHeaderWords +
      packedCapacityWords 0 (capacityWords 8192 full.length 0 (treeSize 0 full)) (wordBits full.length) +
      8192 * (full.length + 0 + treeSize 0 full + 1) := by
  rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080
