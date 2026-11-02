module

public import PaperProofs.Structure.PSTR_RuntimeMarkUsed_011

/-! The physical one-store mark changes exactly one stream bit. This is the
bit-level bridge used to refine the existing logical used bitmap, not a new
encoding or a replacement for the original HeapRepresents predicate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRMarkUsedBits

open AlgorithmClaims AlgorithmClaims.PackedCapacityRAM CompactControllerClaims
open PSTRRuntimeMarkUsed

def bitAt {bits : Nat} (heap : BitVec bits → BitVec bits) (offset : Nat) : Bool :=
  (heap (BitVec.ofNat bits (4 + offset / bits))).getLsbD (offset % bits)

theorem shifted_one_bit {bits : Nat} (hb : 0 < bits) (shift i : Nat) (hi : i < bits) :
    ((BitVec.ofNat bits 1) <<< shift).getLsbD i = decide (i = shift) := by
  simp only [BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_one, hb]
  by_cases hlt : i < shift
  · have hne : i ≠ shift := ne_of_lt hlt
    simp only [hlt, decide_true, Bool.not_true, Bool.false_and, hne, decide_false]
  · have he : i - shift = 0 ↔ i = shift := by omega
    simp only [hlt, decide_false, Bool.not_false, Bool.true_and, he]

theorem mark_bit {bits : Nat} (heap : BitVec bits → BitVec bits) (start offset : Nat)
    (hb : 0 < bits) (hs : Fits bits (4 + start / bits)) (ho : Fits bits (4 + offset / bits)) :
    bitAt (markHeap start heap) offset = if offset = start then true else bitAt heap offset := by
  by_cases hd : offset / bits = start / bits
  · have wordeq : BitVec.ofNat bits (4 + offset / bits) =
        BitVec.ofNat bits (4 + start / bits) := by rw [hd]
    have same : offset % bits = start % bits ↔ offset = start := by
      constructor
      · intro hm
        calc
          offset = bits * (offset / bits) + offset % bits := (Nat.div_add_mod offset bits).symm
          _ = bits * (start / bits) + start % bits := by rw [hd, hm]
          _ = start := Nat.div_add_mod start bits
      · intro he
        rw [he]
    simp only [bitAt, markHeap, Function.update_apply, wordeq, ite_true, BitVec.getLsbD_or,
      shifted_one_bit hb _ _ (Nat.mod_lt offset hb), same]
    by_cases he : offset = start
    · simp only [he, decide_true, Bool.or_true, ite_true]
    · simp only [he, decide_false, Bool.or_false, ite_false]
  · have hneq : BitVec.ofNat bits (4 + offset / bits) ≠ BitVec.ofNat bits (4 + start / bits) :=
      (ofNat_injective_of_fit _ _ ho hs).not.mpr (by omega)
    have hne : offset ≠ start := by intro he; exact hd (congrArg (· / bits) he)
    simp only [bitAt, markHeap, Function.update_of_ne hneq, hne, ite_false]

theorem physical_fit_of_offset {bits : Nat} (offset region : Nat)
    (ho : offset < region) (hr : Fits bits (4 + region)) : Fits bits (4 + offset / bits) := by
  exact (Nat.add_le_add_left (Nat.div_le_self offset bits) 4).trans_lt
    ((Nat.add_lt_add_left ho 4).trans hr)

theorem scalar_stream {bits q : Nat} (heap : BitVec bits → BitVec bits) (capWords address : Nat)
    (hq : 0 < q) (ha : address < capWords) (hr : Fits bits (4 + capWords * CapacityBits.width q)) :
    logicalHeap q capWords heap address = CapacityBits.decodeScalar
      (List.ofFn (fun i : Fin (CapacityBits.width q) => bitAt heap (address * CapacityBits.width q + i.val))) := by
  simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, ha, ite_true]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext i
  have hm : (address + 1) * CapacityBits.width q ≤ capWords * CapacityBits.width q :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
  have hoff : address * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hi := i.isLt
    omega
  have hof : Fits bits ((address * CapacityBits.width q + i.val) / bits) :=
    (Nat.div_le_self _ _).trans_lt (hoff.trans (by
      exact (Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr))
  rw [PSTRRuntimePackedRead.dataHeap_at heap _ hof]
  rfl

theorem zero_scalar_bits {bits q : Nat} (heap : BitVec bits → BitVec bits) (capWords address : Nat)
    (hq : 0 < q) (ha : address < capWords) (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hz : logicalHeap q capWords heap address = 0) (i : Fin (CapacityBits.width q)) :
    bitAt heap (address * CapacityBits.width q + i.val) = false := by
  rw [scalar_stream heap capWords address hq ha hr] at hz
  let stream := List.ofFn (fun i : Fin (CapacityBits.width q) => bitAt heap (address * CapacityBits.width q + i.val))
  have he : BitVec.ofBoolListLE stream = BitVec.ofNat stream.length 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [CapacityBits.decodeScalar, BitVec.toNat_ofNat, Nat.zero_mod] using hz
  have hbit := congrArg (fun value : BitVec stream.length => value.getLsbD i.val) he
  rw [BitVec.getLsbD_ofBoolListLE] at hbit
  have hi : i.val < stream.length := by simpa only [stream, List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ false hi] at hbit
  simpa only [stream, List.getElem_ofFn, BitVec.getLsbD_zero] using hbit

theorem mark_scalar_target {bits q : Nat} (heap : BitVec bits → BitVec bits) (capWords address : Nat)
    (hb : 0 < bits) (hq : 0 < q) (ha : address < capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hz : logicalHeap q capWords heap address = 0) :
    logicalHeap q capWords (markHeap (address * CapacityBits.width q) heap) address = 1 := by
  have hw : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hm : (address + 1) * CapacityBits.width q ≤ capWords * CapacityBits.width q :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
  have hs : address * CapacityBits.width q < capWords * CapacityBits.width q := by
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  have hsfit := physical_fit_of_offset (bits := bits) _ _ hs hr
  rw [scalar_stream _ capWords address hq ha hr]
  have he : (List.ofFn (fun i : Fin (CapacityBits.width q) =>
      bitAt (markHeap (address * CapacityBits.width q) heap) (address * CapacityBits.width q + i.val))) =
      CapacityBits.encodeScalar (CapacityBits.width q) 1 := by
    unfold CapacityBits.encodeScalar
    apply congrArg List.ofFn
    funext i
    have ho : address * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
      rw [Nat.add_mul, Nat.one_mul] at hm
      have hi := i.isLt
      omega
    rw [mark_bit heap _ _ hb hsfit (physical_fit_of_offset _ _ ho hr)]
    by_cases hi : i.val = 0
    · simp only [hi, Nat.add_zero, ite_true, BitVec.getLsbD_one, hw, decide_true, Bool.and_self]
    · have hne : address * CapacityBits.width q + i.val ≠ address * CapacityBits.width q := by omega
      rw [ite_eq_right hne, zero_scalar_bits heap capWords address hq ha hr hz i]
      simp only [BitVec.getLsbD_one, hw, decide_true, hi, decide_false, Bool.true_and]
  rw [he, CapacityBits.decodeScalar_encode_bounded q 1 hq]

theorem mark_other_capacity {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords address other : Nat) (hb : 0 < bits) (hq : 0 < q)
    (ha : address < capWords) (ho : other < capWords) (hne : other ≠ address)
    (hr : Fits bits (4 + capWords * CapacityBits.width q)) :
    logicalHeap q capWords (markHeap (address * CapacityBits.width q) heap) other =
      logicalHeap q capWords heap other := by
  have hw : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hma := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt ha)
  have hs : address * CapacityBits.width q < capWords * CapacityBits.width q := by
    rw [Nat.succ_mul] at hma
    omega
  rw [scalar_stream _ _ _ hq ho hr, scalar_stream _ _ _ hq ho hr]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext i
  have hmo := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt ho)
  have hoff : other * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
    rw [Nat.succ_mul] at hmo
    have hi := i.isLt
    omega
  have hd : other * CapacityBits.width q + i.val ≠ address * CapacityBits.width q := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hh := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at hh
      have hi := i.isLt
      omega
    · have hh := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at hh
      omega
  rw [mark_bit heap _ _ hb (physical_fit_of_offset _ _ hs hr)
    (physical_fit_of_offset _ _ hoff hr), ite_eq_right hd]

end PaperProofs.Structure.LaminarTree.PSTRMarkUsedBits
