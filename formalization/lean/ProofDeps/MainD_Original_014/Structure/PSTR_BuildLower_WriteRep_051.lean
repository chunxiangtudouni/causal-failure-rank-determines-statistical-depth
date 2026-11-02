module

public import Structure.PSTR_BuildLower_SourceRep_048

/-! The actual replacement heap of the frozen writer refines a source store.
Its low physical writes preserve the high VM bank. Old capacity cutoff and
new packed allocation remain distinct; ordinary metadata is not bit packed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
variable {bits : Nat}

private theorem target_address (state : WordState bits) (pointer : Register) (C0 indexBase a : Nat)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase) :
    Ordinary.targetAddress state pointer = BitVec.ofNat bits (indexBase + (a - C0)) := by
  have hb : state.heap (state.register .address + BitVec.ofNat bits 6) = BitVec.ofNat bits indexBase := by
    rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [Ordinary.targetAddress, hp, hc, hb, BitVec.ofNat_add_ofNat]

theorem write_high_frame (q C0 C indexBase I a point : Nat) (state : WordState bits) (pointer : Register)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase)
    (hq : 0 < q) (hb : 0 < bits) (hC : C0 ≤ C) (had : a < C0 + I)
    (hpacked : 4 + packedCapacityWords q C bits + 1 ≤ indexBase + I)
    (hpoint : indexBase + I ≤ point) (hfit : Fits bits point) :
    ConcreteHeap.writeViewHeap q state pointer (BitVec.ofNat bits point) = state.heap (BitVec.ofNat bits point) := by
  by_cases ha : a < C0
  · have hn : ¬DispatchRun.ordinaryCase pointer state := by
      change ¬(state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    have hw : 0 < CapacityBits.width q := by
      by_contra hn
      have hz : CapacityBits.width q = 0 := by omega
      have hqz := (CapacityBits.width_eq_zero_iff q).mp hz
      omega
    have hl : a * CapacityBits.width q / bits < packedCapacityWords q C bits :=
      (Nat.div_lt_iff_lt_mul hb).mpr
        ((Nat.mul_lt_mul_of_pos_right (ha.trans_le hC) hw).trans_le (packedCapacityWords_mul_bits q C hb))
    have hlow : 4 + a * CapacityBits.width q / bits < point := by omega
    have hhigh : 4 + (a * CapacityBits.width q / bits + 1) < point := by omega
    have hnlow : BitVec.ofNat bits point ≠ BitVec.ofNat bits (4 + a * CapacityBits.width q / bits) :=
      word_address_ne hfit (hlow.trans hfit) (by omega)
    have hnhigh : BitVec.ofNat bits point ≠ BitVec.ofNat bits (4 + (a * CapacityBits.width q / bits + 1)) :=
      word_address_ne hfit (hhigh.trans hfit) (by omega)
    rw [ConcreteHeap.writeViewHeap, ite_eq_right hn, hp, ViewStep.physicalWrite_eq]
    simp only [PA06A19PreparePackedView013.packedStore, Function.update_of_ne hnhigh, Function.update_of_ne hnlow]
  · have hg : DispatchRun.ordinaryCase pointer state := by
      change (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    have ht : indexBase + (a - C0) < point := by omega
    have hn : BitVec.ofNat bits point ≠ BitVec.ofNat bits (indexBase + (a - C0)) :=
      word_address_ne hfit (ht.trans hfit) (by omega)
    rw [ConcreteHeap.writeViewHeap, ite_eq_left hg, target_address state pointer C0 indexBase a hp hc hi,
      Function.update_of_ne hn]

theorem store_replacement (q C0 C indexBase I base : Nat) (source : PhysicalROM)
    (logical : State) (state after : WordState bits) (pointer sourceReg : Register)
    (hrep : Represents q C0 C indexBase I base logical state)
    (hp : (Ordinary.pointerValue state pointer).toNat = logical.register pointer)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase)
    (hv : (state.register .value).toNat = logical.register sourceReg)
    (hheap : after.heap = ConcreteHeap.writeViewHeap q state pointer)
    (haddress : after.register .address = state.register .address)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits) (hC : C0 ≤ C)
    (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hend : Fits bits (indexBase + I)) (had : logical.register pointer < C0 + I)
    (hnext : logical.register pointer < C0 → Fits bits (logical.register pointer * CapacityBits.width q / bits + 1))
    (hvalue : logical.register pointer < C0 → logical.register sourceReg ≤ q)
    (hpacked : 4 + packedCapacityWords q C bits + 1 ≤ indexBase + I)
    (hdisjoint : indexBase + I ≤ base + 32) (hbank : Fits bits (base + 39)) :
    Represents q C0 C indexBase I base
      ((Op.base (.storeHeap pointer sourceReg)).execute source.semantic logical) after := by
  refine ⟨haddress.trans hrep.address, ?_, ?_⟩
  · funext reg
    have hlo := (registerSlot_bounds reg).1
    have hhi := (registerSlot_bounds reg).2
    change 32 ≤ registerOffset reg at hlo
    change registerOffset reg < 39 at hhi
    have hpfit : Fits bits (base + registerOffset reg) := lt_trans (by omega) hbank
    have hh := write_high_frame q C0 C indexBase I (logical.register pointer) (base + registerOffset reg)
      state pointer hp hc hi hq hb hC had hpacked (by omega) hpfit
    change after.heap (BitVec.ofNat bits base + BitVec.ofNat bits (registerOffset reg)) = _
    rw [hheap, BitVec.ofNat_add_ofNat, hh]
    simpa only [portRegisters, BitVec.ofNat_add_ofNat, Op.execute, Instruction.execute] using congrFun hrep.registers reg
  · intro other ho
    rw [hheap, ViewStep.writeView_update q C0 C indexBase I (logical.register pointer) state pointer hp hc hi
      hb hw hC hregion hbase hend had hnext (by intro h; rw [hv]; exact hvalue h) other ho, hv]
    change (Function.update (PA06A19PreparePackedView013.view q C0 C indexBase state.heap)
      (logical.register pointer) (logical.register sourceReg)) other =
      (Function.update logical.heap (logical.register pointer) (logical.register sourceReg)) other
    by_cases he : other = logical.register pointer
    · subst other
      simp only [Function.update_self]
    · simp only [Function.update_of_ne he]
      exact hrep.heap other ho

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
