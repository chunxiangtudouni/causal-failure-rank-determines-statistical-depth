module

public import Structure.PSTR_BuildLower_ResourceTrace_094
public import Structure.PSTR_BuildLower_WriteData_070

/-! Full NEW-C capacity of the actual writer replacement, including cells
outside the finite C0 source view. The two physical branches use the frozen
packed-store/index-store lemmas on the SAME heap. This is an endpoint fact;
actual-prefix transport is a separate obligation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.GlobalCapacity
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem write_replacement (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (pointer : Register)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (hvalue : logical.register pointer < oldCapacity q full → (state.register .value).toNat ≤ q)
    (bounded : Bounded q full state.heap) :
    Bounded q full (ConcreteHeap.writeViewHeap q state pointer) := by
  have hp := SourceRep.pointer_nat q full logical state hrep pointer hptr
  have hc := RuntimeData.Data.cutoff_nat q full hq state data hrep.address
  have hi := RuntimeData.Data.index_nat q full hq state data hrep.address
  unfold Bounded at bounded ⊢
  simp only [CompactControllerClaims.logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] at bounded ⊢
  by_cases hordinary : DispatchRun.ordinaryCase pointer state
  · have hge : oldCapacity q full ≤ logical.register pointer := by
      simpa only [DispatchRun.ordinaryCase, hc, hp] using hordinary
    have hidx : state.heap (state.register .address + BitVec.ofNat _ 6) = BitVec.ofNat _ (indexBase q full) := by
      rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have target : Ordinary.targetAddress state pointer =
        BitVec.ofNat _ (indexBase q full + (logical.register pointer - oldCapacity q full)) := by
      simp only [Ordinary.targetAddress, hp, hc, hidx, BitVec.ofNat_add_ofNat]
    rw [ConcreteHeap.writeViewHeap, ite_eq_left hordinary, target]
    exact PA06A19PreparePackedView013.indexStore_capacityBounded q (oldCapacity q full) (capacity q full)
      (indexBase q full) (logical.register pointer) (state.register .value) state.heap
      (by have hh := bits_room q full; omega) (capacity_product_fits q full hq)
      le_rfl (lt_trans (by omega) (ordinary_end_fits q full hq)) bounded
  · have hlt : logical.register pointer < oldCapacity q full := by
      change ¬(state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat at hordinary
      rw [hp, hc] at hordinary
      omega
    rw [ConcreteHeap.writeViewHeap, ite_eq_right hordinary, hp, ViewStep.physicalWrite_eq]
    exact PA06A19PreparePackedView013.packedStore_capacityBounded q (capacity q full) (logical.register pointer)
      (state.register .value) state.heap (by have hh := bits_room q full; omega) (width_room q full)
      (hlt.trans_le (oldCapacity_le q full hq))
      (lt_of_le_of_lt (by omega) (packed_next q full hq (logical.register pointer) hlt))
      (capacity_product_fits q full hq) (hvalue hlt) bounded

theorem write_replacement_cache (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (pointer : Register)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full) :
    ResourceTrace.CacheFrame q full state.heap (ConcreteHeap.writeViewHeap q state pointer) := by
  intro point hp hf
  exact SourceRep.write_high_frame q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full)
    (logical.register pointer) point state pointer (SourceRep.pointer_nat q full logical state hrep pointer hptr)
    (RuntimeData.Data.cutoff_nat q full hq state data hrep.address) (RuntimeData.Data.index_nat q full hq state data hrep.address)
    hq (by have hh := bits_room q full; omega) (oldCapacity_le q full hq) had (packed_lookahead_before_end q full)
    (by have hh := ordinary_before_control q full; omega) hf

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.GlobalCapacity
