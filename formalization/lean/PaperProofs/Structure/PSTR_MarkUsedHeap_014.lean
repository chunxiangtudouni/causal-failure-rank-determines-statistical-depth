module

public import PaperProofs.Structure.PSTR_MarkUsedBits_012
public import PaperProofs.Structure.PA17_RequestPaths_016

/-! Refine the real one-store mark to the ORIGINAL controller HeapRepresents.
Only the used set changes in this component; advancing stage and preserving
reply registers are later actual-call obligations. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRMarkUsedHeap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims
open PSTRRuntimeMarkUsed PSTRMarkUsedBits

theorem mark_index {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords address other : Nat) (hb : 0 < bits) (hq : 0 < q)
    (ha : address < capWords) (ho : capWords ≤ other)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : Fits bits (4 + packedCapacityWords q capWords bits + (other - capWords))) :
    logicalHeap q capWords (markHeap (address * CapacityBits.width q) heap) other =
      logicalHeap q capWords heap other := by
  have hw : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : address * CapacityBits.width q < capWords * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right ha hw
  have hword : address * CapacityBits.width q / bits < packedCapacityWords q capWords bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr (hstart.trans_le (packedCapacityWords_mul_bits q capWords hb))
  have hsfit := physical_fit_of_offset _ _ hstart hr
  have hid : Fits bits (packedCapacityWords q capWords bits + (other - capWords)) :=
    (show packedCapacityWords q capWords bits + (other - capWords) ≤
      4 + packedCapacityWords q capWords bits + (other - capWords) by omega).trans_lt hi
  simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, not_lt_of_ge ho]
  rw [PSTRRuntimePackedRead.dataHeap_at _ _ hid, PSTRRuntimePackedRead.dataHeap_at _ _ hid]
  apply congrArg BitVec.toNat
  apply markHeap_frame
  have hlt : 4 + address * CapacityBits.width q / bits <
      4 + packedCapacityWords q capWords bits + (other - capWords) :=
    (Nat.add_lt_add_left hword 4).trans_le (Nat.le_add_right _ _)
  simpa only [Nat.add_assoc] using (ofNat_injective_of_fit _ _ hi hsfit).not.mpr (ne_of_gt hlt)

theorem mark_capacity_bounded {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords address : Nat) (hb : 0 < bits) (hq : 0 < q) (ha : address < capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hz : logicalHeap q capWords heap address = 0)
    (bounded : CapacityPrefixBounded q capWords (logicalHeap q capWords heap)) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (markHeap (address * CapacityBits.width q) heap)) := by
  intro other ho
  by_cases he : other = address
  · subst other
    rw [mark_scalar_target heap capWords address hb hq ha hr hz]
    exact hq
  · rw [mark_other_capacity heap capWords address other hb hq ha ho he hr]
    exact bounded other ho

theorem heapRepresents_insert {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (tool : Fin q) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset)) :
    HeapRepresents q full capWords { configuration with used := insert tool configuration.used }
      (markHeap ((tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q) heap) := by
  let address := tableWords full.length q (treeSize q full) + tool.val
  have ha : address < capWords := by dsimp only [address]; have ht := tool.isLt; omega
  have hw : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : address * CapacityBits.width q < capWords * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right ha hw
  have hptr := physical_fit_of_offset _ _ hstart hr
  have hhead (header : Nat) (hh : header < 4) :
      markHeap (address * CapacityBits.width q) heap (BitVec.ofNat bits header) =
        heap (BitVec.ofNat bits header) := markHeap_header _ heap hb hptr header hh
  have hindex (offset : Nat) (hoff : offset < 2 + (staticMetadata q full).length) :
      logicalHeap q capWords (markHeap (address * CapacityBits.width q) heap) (capWords + offset) =
        logicalHeap q capWords heap (capWords + offset) := by
    apply mark_index heap capWords address (capWords + offset) (by omega) hq ha (Nat.le_add_right _ _) hr
    simpa only [Nat.add_sub_cancel_left] using hi offset hoff
  dsimp only [HeapRepresents] at rep ⊢
  obtain ⟨ht, hc, hp, hbits, hstage, hfailed, hmetadata, hused, htable⟩ := rep
  have hz : logicalHeap q capWords heap address = 0 := by
    simpa only [address, unused, decide_false, bit, Bool.false_eq_true, ite_false] using hused tool
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hhead 0 (by decide)]; exact ht
  · rw [hhead 1 (by decide)]; exact hc
  · rw [hhead 2 (by decide)]; exact hp
  · rw [hhead 3 (by decide)]; exact hbits
  · have hs := hindex 0 (by omega)
    simpa only [Nat.add_zero] using hs.trans hstage
  · exact (hindex 1 (by omega)).trans hfailed
  · intro position hposition
    have hf := hindex (2 + position) (by omega)
    have hm : logicalHeap q capWords heap (capWords + (2 + position)) =
        (staticMetadata q full)[position] := by
      simpa only [Nat.add_assoc] using hmetadata position hposition
    simpa only [Nat.add_assoc] using hf.trans hm
  · intro other
    by_cases he : other = tool
    · subst other
      have hone := mark_scalar_target heap capWords address (by omega) hq ha hr hz
      simpa only [address, Finset.mem_insert_self, decide_true, bit, ite_true] using hone
    · have hoa : tableWords full.length q (treeSize q full) + other.val < capWords := by
        have ho := other.isLt
        omega
      have hne : tableWords full.length q (treeSize q full) + other.val ≠ address := by
        intro hval
        apply he
        apply Fin.ext
        exact Nat.add_left_cancel hval
      rw [mark_other_capacity heap capWords address _ (by omega) hq ha hoa hne hr]
      simpa only [Finset.mem_insert, he, false_or] using hused other
  · intro hpositive
    have hsize : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
      simp only [treeSize, ne_of_gt hq, ite_false]
    refine ⟨?_, mark_capacity_bounded heap capWords address (by omega) hq ha hr hz (htable hpositive).2⟩
    apply PA17RequestPaths016.physicalTableCorrect_of_frame q full _ _ (htable hpositive).1
    intro index hidx
    have hsmall : index < tableWords full.length q (treeSize q full) := by
      simpa only [hsize] using hidx
    have hic : index < capWords := hsmall.trans_le (by omega)
    have hne : index ≠ address := by dsimp only [address]; omega
    exact mark_other_capacity heap capWords address index (by omega) hq ha hic hne hr

theorem actual_insert {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 14 state
    after.halted = true ∧ HeapRepresents q full capWords
      { configuration with used := insert tool configuration.used } after.heap := by
  have haddr : (state.register .address).toNat < capWords := by
    rw [haddress]
    have ht := tool.isLt
    omega
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) :=
    (Nat.mul_lt_mul_of_pos_right haddr hwp).trans
      ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  have hheader : (state.heap (BitVec.ofNat bits 3)).toNat = bits := rep.2.2.2.1
  have result := PSTRRuntimeMarkUsed.actual_run rom state hb hw hwidth hheader hstart hp ha
  dsimp only at result ⊢
  refine ⟨result.1, ?_⟩
  rw [result.2, haddress]
  exact heapRepresents_insert full configuration capWords state.heap tool hb hq rep unused bitmap hr hi

end PaperProofs.Structure.LaminarTree.PSTRMarkUsedHeap
