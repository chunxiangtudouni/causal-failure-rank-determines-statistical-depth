module

public import Structure.PA06_A19Prepare_FiniteClear025_Virtual
public import Structure.PA06_A19Prepare_PackedView013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteInit038VirtualFrame

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)
open PA06A19PreparePackedView013 (view)

variable {bits : Nat}

/-- A physical low-region frame transports genuine packed values. The real
lookahead word is included, so the boundary scalar is not silently omitted. -/
theorem unpack_lower_frame (q C cutoff : Nat) (first second : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hregion : 4 + packedCapacityWords q C bits < cutoff) (hfit : Fits bits cutoff)
    (hframe : ∀ point : BitVec bits, point.toNat < cutoff → second point = first point)
    (a : Nat) (ha : a < C) :
    unpackHeap q C bits (dataHeap second) a = unpackHeap q C bits (dataHeap first) a := by
  have hwp : 0 < CapacityBits.width q := by
    by_contra hn
    have he : CapacityBits.width q = 0 := by omega
    have heq := (CapacityBits.width_eq_zero_iff q).mp he
    omega
  have hprod : a * CapacityBits.width q < C * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right ha hwp
  have hlow : a * CapacityBits.width q / bits < packedCapacityWords q C bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr (hprod.trans_le (packedCapacityWords_mul_bits q C hb))
  have word_eq (word : Nat) (hword : word ≤ packedCapacityWords q C bits) :
      dataHeap second (BitVec.ofNat bits word) = dataHeap first (BitVec.ofNat bits word) := by
    rw [PA06A19PreparePackedView013.dataHeap_word, PA06A19PreparePackedView013.dataHeap_word]
    apply hframe
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by omega : 4 + word < cutoff).trans hfit)]
    omega
  rw [← readTwoWords_eq_unpackHeap q C a (dataHeap second) hb hw ha,
    ← readTwoWords_eq_unpackHeap q C a (dataHeap first) hb hw ha,
    word_eq _ hlow.le, word_eq _ (by omega)]

theorem view_lower_frame (q C0 C I cutoff : Nat) (first second : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hC : C0 ≤ C) (hI : 0 < I)
    (hregion : 4 + (packedCapacityWords q C bits + I) ≤ cutoff) (hfit : Fits bits cutoff)
    (hframe : ∀ point : BitVec bits, point.toNat < cutoff → second point = first point)
    (a : Nat) (ha : a < C0 + I) :
    view q C0 C (4 + packedCapacityWords q C bits) second a =
      view q C0 C (4 + packedCapacityWords q C bits) first a := by
  by_cases hc : a < C0
  · rw [PA06A19PreparePackedView013.view_capacity q C0 C _ second a hc,
      PA06A19PreparePackedView013.view_capacity q C0 C _ first a hc]
    exact unpack_lower_frame q C cutoff first second hq hb hw (by omega) hfit hframe a (hc.trans_le hC)
  · have hlo : C0 ≤ a := by omega
    rw [PA06A19PreparePackedView013.view_index q C0 C _ second a hlo,
      PA06A19PreparePackedView013.view_index q C0 C _ first a hlo]
    apply congrArg BitVec.toNat
    apply hframe
    have hn : 4 + packedCapacityWords q C bits + (a - C0) < cutoff := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hn.trans hfit)]
    exact hn

/-- The executed 22-op wipe writes only CB+32..38 and preserves every
physical word strictly below CB. Its placement and code qualifications are
ordinary internal segment obligations, not zero-heap assumptions. -/
theorem body_lower_frame (rom : PhysicalROM) (left right : List PackingOp) (before : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)))
    (hpcCode : Fits bits (5 * (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right).length))
    (hpc : before.pc = BitVec.ofNat bits (5 * left.length)) (ha : before.halted = false)
    (hfit : Fits bits ((before.register .address).toNat + 38))
    (point : BitVec bits) (hpoint : point.toNat < (before.register .address).toNat) :
    (packingRun rom (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) 22 before).heap point = before.heap point := by
  apply PA06A19PrepareFiniteClear025Virtual.body_frame rom left right before hcode hpcCode hpc ha point
  intro slot hslot
  have hs : slot ≤ 38 := by
    change slot ∈ [32, 33, 34, 35, 36, 37, 38] at hslot
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
    omega
  have hoff : Fits bits slot := (by omega : slot ≤ (before.register .address).toNat + 38).trans_lt hfit
  have hsum : Fits bits ((before.register .address).toNat + slot) :=
    (by omega : (before.register .address).toNat + slot ≤ (before.register .address).toNat + 38).trans_lt hfit
  intro heq
  have hn := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hsum] at hn
  omega

/-- The actual VM wipe preserves the initialized old finite builder view. -/
theorem body_view (rom : PhysicalROM) (left right : List PackingOp) (before : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right)))
    (hpcCode : Fits bits (5 * (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right).length))
    (hpc : before.pc = BitVec.ofNat bits (5 * left.length)) (ha : before.halted = false)
    (hfit : Fits bits ((before.register .address).toNat + 38))
    (q C0 C I : Nat) (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hC : C0 ≤ C) (hI : 0 < I)
    (hregion : 4 + (packedCapacityWords q C bits + I) ≤ (before.register .address).toNat)
    (a : Nat) (ha0 : a < C0 + I) :
    view q C0 C (4 + packedCapacityWords q C bits)
      (packingRun rom (left ++ PA06A19PrepareFiniteClear025.clearVirtual ++ right) 22 before).heap a =
        view q C0 C (4 + packedCapacityWords q C bits) before.heap a := by
  exact view_lower_frame q C0 C I (before.register .address).toNat before.heap _ hq hb hw hC hI
    hregion ((Nat.le_add_right _ _).trans_lt hfit)
    (body_lower_frame rom left right before hcode hpcCode hpc ha hfit) a ha0

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteInit038VirtualFrame
