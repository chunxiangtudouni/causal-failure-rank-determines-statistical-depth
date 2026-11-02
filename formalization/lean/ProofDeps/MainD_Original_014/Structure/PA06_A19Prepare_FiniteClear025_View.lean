module

public import Structure.PA06_A19Prepare_PackedView013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

/-! Uncompiled finite zero-initial-view consequence. Only the physically
allocated packed words plus one real lookahead and the finite old ordinary
domain are zero. No infinite Word heap or original caller is assumed zero.
The actual clear025 Result discharges these finite store facts in assembly.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025View

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)
open PA06A19PreparePackedView013 (view)

variable {bits : Nat}

theorem unpack_zero_of_finite_words (q C : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hz : ∀ word ≤ packedCapacityWords q C bits, heap (BitVec.ofNat bits (4 + word)) = 0)
    (a : Nat) (ha : a < C) :
    unpackHeap q C bits (dataHeap heap) a = 0 := by
  have hwp : 0 < CapacityBits.width q := by
    by_contra hn
    have he : CapacityBits.width q = 0 := by omega
    have heq := (CapacityBits.width_eq_zero_iff q).mp he
    omega
  have hprod : a * CapacityBits.width q < C * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right ha hwp
  have hlow : a * CapacityBits.width q / bits < packedCapacityWords q C bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr (hprod.trans_le (packedCapacityWords_mul_bits q C hb))
  rw [← readTwoWords_eq_unpackHeap q C a (dataHeap heap) hb hw ha,
    PA06A19PreparePackedView013.dataHeap_word,
    PA06A19PreparePackedView013.dataHeap_word,
    hz _ hlow.le, hz _ (by omega)]
  simp [readTwoWords]

theorem view_zero_of_finite_words (q C0 C I : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits) (hC : C0 ≤ C)
    (hz : ∀ word ≤ packedCapacityWords q C bits, heap (BitVec.ofNat bits (4 + word)) = 0)
    (hi : ∀ index < I, heap (BitVec.ofNat bits (4 + packedCapacityWords q C bits + index)) = 0)
    (a : Nat) (ha : a < C0 + I) :
    view q C0 C (4 + packedCapacityWords q C bits) heap a = 0 := by
  by_cases hc : a < C0
  · rw [PA06A19PreparePackedView013.view_capacity q C0 C _ heap a hc]
    exact unpack_zero_of_finite_words q C heap hq hb hw hz a (hc.trans_le hC)
  · have hlo : C0 ≤ a := by omega
    rw [PA06A19PreparePackedView013.view_index q C0 C _ heap a hlo, hi (a - C0) (by omega)]
    simp

theorem capacity_bounded_of_finite_zero (q C : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hz : ∀ word ≤ packedCapacityWords q C bits, heap (BitVec.ofNat bits (4 + word)) = 0) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap)) := by
  intro a ha
  rw [unpack_zero_of_finite_words q C heap hq hb hw hz a ha]
  exact Nat.zero_le _

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025View
