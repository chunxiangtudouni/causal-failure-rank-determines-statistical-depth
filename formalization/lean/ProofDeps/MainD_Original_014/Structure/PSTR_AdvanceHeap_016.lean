module

public import Structure.PSTR_MarkUsedHeap_014
public import Structure.PSTR_RuntimeAdvance_015

/-! The actual stage-word update refines the original configuration heap.
Capacity words and all static metadata are preserved on the same physical
heap; the next-stage fit is explicit until the full live layout supplies it. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRAdvanceHeap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims
open PSTRRuntimeAdvance

theorem bump_header {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hp : Fits bits (4 + packed)) (header : Nat) (hh : header < 4) :
    bumpHeap packed heap (BitVec.ofNat bits header) = heap (BitVec.ofNat bits header) := by
  apply heap_frame
  have hbits := Nat.lt_two_pow_self (n := bits)
  have hf : Fits bits header := hh.trans (show 4 < 2 ^ bits by omega)
  apply (ofNat_injective_of_fit header (4 + packed) hf hp).not.mpr
  omega

theorem bump_capacity {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords address : Nat) (hb : 0 < bits) (hq : 0 < q) (ha : address < capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hp : Fits bits (4 + packedCapacityWords q capWords bits)) :
    logicalHeap q capWords (bumpHeap (packedCapacityWords q capWords bits) heap) address =
      logicalHeap q capWords heap address := by
  rw [PSTRMarkUsedBits.scalar_stream _ _ _ hq ha hr,
    PSTRMarkUsedBits.scalar_stream _ _ _ hq ha hr]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext i
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at hm
  have hoff : address * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
    have hi := i.isLt
    omega
  have hd : (address * CapacityBits.width q + i.val) / bits <
      packedCapacityWords q capWords bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr
      (hoff.trans_le (packedCapacityWords_mul_bits q capWords hb))
  unfold PSTRMarkUsedBits.bitAt
  rw [heap_frame]
  apply (ofNat_injective_of_fit _ _
    (PSTRMarkUsedBits.physical_fit_of_offset _ _ hoff hr) hp).not.mpr
  omega

theorem bump_index {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords offset : Nat) (hq : 0 < q)
    (hi : Fits bits (4 + packedCapacityWords q capWords bits + offset)) :
    logicalHeap q capWords (bumpHeap (packedCapacityWords q capWords bits) heap)
      (capWords + offset) =
      if offset = 0 then
        (bumpHeap (packedCapacityWords q capWords bits) heap
          (BitVec.ofNat bits (4 + packedCapacityWords q capWords bits))).toNat
      else logicalHeap q capWords heap (capWords + offset) := by
  have hnot : ¬capWords + offset < capWords := by omega
  have hid : Fits bits (packedCapacityWords q capWords bits + offset) := by
    exact (show packedCapacityWords q capWords bits + offset ≤
      4 + packedCapacityWords q capWords bits + offset by omega).trans_lt hi
  simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, hnot,
    Nat.add_sub_cancel_left]
  rw [PSTRRuntimePackedRead.dataHeap_at _ _ hid, PSTRRuntimePackedRead.dataHeap_at _ _ hid]
  by_cases he : offset = 0
  · subst offset
    simp only [Nat.add_zero, ite_true]
  · rw [ite_eq_right he, heap_frame]
    have hp : Fits bits (4 + packedCapacityWords q capWords bits) :=
      (Nat.le_add_right _ offset).trans_lt hi
    apply (ofNat_injective_of_fit _ _ (by simpa only [Nat.add_assoc] using hi) hp).not.mpr
    omega

theorem heapRepresents_advance {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1)) :
    HeapRepresents q full capWords { configuration with stage := configuration.stage + 1 }
      (bumpHeap (packedCapacityWords q capWords bits) heap) := by
  have hp : Fits bits (4 + packedCapacityWords q capWords bits) := by
    simpa only [Nat.add_zero] using hi 0 (by omega)
  have hindex (offset : Nat) (hoff : offset < 2 + (staticMetadata q full).length)
      (hne : offset ≠ 0) :
      logicalHeap q capWords (bumpHeap (packedCapacityWords q capWords bits) heap)
          (capWords + offset) = logicalHeap q capWords heap (capWords + offset) := by
    rw [bump_index heap capWords offset hq (hi offset hoff), ite_eq_right hne]
  have hcurrent : (heap (BitVec.ofNat bits (4 + packedCapacityWords q capWords bits))).toNat =
      configuration.stage := by
    have hid : Fits bits (packedCapacityWords q capWords bits) :=
      (Nat.le_add_left _ 4).trans_lt hp
    have hc := rep.2.2.2.2.1
    simpa only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, lt_self_iff_false,
      Nat.sub_self, Nat.add_zero, PSTRRuntimePackedRead.dataHeap_at _ _ hid] using hc
  dsimp only [HeapRepresents] at rep ⊢
  obtain ⟨ht, hc, hphead, hbits, hstage, hfailed, hmetadata, hused, htable⟩ := rep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bump_header _ heap hb hp 0 (by decide)]; exact ht
  · rw [bump_header _ heap hb hp 1 (by decide)]; exact hc
  · rw [bump_header _ heap hb hp 2 (by decide)]; exact hphead
  · rw [bump_header _ heap hb hp 3 (by decide)]; exact hbits
  · have hs := bump_index heap capWords 0 hq (hi 0 (by omega))
    simpa only [Nat.add_zero, ite_true] using hs.trans (stage_word _ _ heap hcurrent hnext)
  · exact (hindex 1 (by omega) (by decide)).trans hfailed
  · intro position hposition
    have hf := hindex (2 + position) (by omega) (by omega)
    have hm : logicalHeap q capWords heap (capWords + (2 + position)) =
        (staticMetadata q full)[position] := by
      simpa only [Nat.add_assoc] using hmetadata position hposition
    simpa only [Nat.add_assoc] using hf.trans hm
  · intro tool
    rw [bump_capacity heap capWords _ (by omega) hq (by have ht := tool.isLt; omega) hr hp]
    exact hused tool
  · intro hpositive
    have hsize : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
      simp only [treeSize, ne_of_gt hq, ite_false]
    refine ⟨?_, ?_⟩
    · apply PA17RequestPaths016.physicalTableCorrect_of_frame q full _ _ (htable hpositive).1
      intro index hidx
      have hsmall : index < tableWords full.length q (treeSize q full) := by
        simpa only [hsize] using hidx
      exact bump_capacity heap capWords index (by omega) hq (hsmall.trans_le (by omega)) hr hp
    · intro address ha
      rw [bump_capacity heap capWords address (by omega) hq ha hr hp]
      exact (htable hpositive).2 address ha

theorem actual_correct {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom PSTRRuntimeAdvance.program 9 state
    after.halted = true ∧ HeapRepresents q full capWords
      (nextConfiguration q full configuration .correct) after.heap := by
  have result := PSTRRuntimeAdvance.actual_run rom state (packedCapacityWords q capWords bits)
    hb rep.2.2.1 hp ha
  dsimp only at result ⊢
  refine ⟨result.1, ?_⟩
  rw [result.2]
  exact heapRepresents_advance full configuration capWords state.heap hb hq rep bitmap hr hi hnext

end PaperProofs.Structure.LaminarTree.PSTRAdvanceHeap
