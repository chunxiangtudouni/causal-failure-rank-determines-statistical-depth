module

public import Structure.PSTR_BuildLower_ConcreteReadExits_067
public import Structure.PSTR_BuildLower_WriteRep_051

/-! Physical source-store replacements preserve real producer data and every
control/lexical word. The low temporary packed Header is protected by actual
physical write addresses>=4; the high bank is beyond the finite source domain. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

theorem write_low_frame (q C0 indexBase I a point : Nat) (state : WordState bits) (pointer : Register)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase)
    (had : a < C0 + I) (hbase : 4 ≤ indexBase) (hend : Fits bits (indexBase + I))
    (hnext : a < C0 → Fits bits (a * CapacityBits.width q / bits + 4 + 1)) (hpoint : point < 4) :
    ConcreteHeap.writeViewHeap q state pointer (BitVec.ofNat bits point) = state.heap (BitVec.ofNat bits point) := by
  by_cases ha : a < C0
  · have hn : ¬DispatchRun.ordinaryCase pointer state := by
      change ¬(state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    have he : 4 + (a * CapacityBits.width q / bits + 1) = a * CapacityBits.width q / bits + 4 + 1 := by omega
    have hh : Fits bits (4 + (a * CapacityBits.width q / bits + 1)) := by rw [he]; exact hnext ha
    have hl : Fits bits (4 + a * CapacityBits.width q / bits) := lt_of_le_of_lt (by omega) hh
    have hpointLow : point < 4 + a * CapacityBits.width q / bits := hpoint.trans_le (Nat.le_add_right _ _)
    have hpointHigh : point < 4 + (a * CapacityBits.width q / bits + 1) := hpoint.trans_le (Nat.le_add_right _ _)
    have hpfit : Fits bits point := hpointLow.trans hl
    have hnl : BitVec.ofNat bits point ≠ BitVec.ofNat bits (4 + a * CapacityBits.width q / bits) :=
      word_address_ne hpfit hl (Nat.ne_of_lt hpointLow)
    have hnh : BitVec.ofNat bits point ≠ BitVec.ofNat bits (4 + (a * CapacityBits.width q / bits + 1)) :=
      word_address_ne hpfit hh (Nat.ne_of_lt hpointHigh)
    rw [ConcreteHeap.writeViewHeap, ite_eq_right hn, hp, ViewStep.physicalWrite_eq]
    simp only [PA06A19PreparePackedView013.packedStore, Function.update_of_ne hnh, Function.update_of_ne hnl]
  · have hg : DispatchRun.ordinaryCase pointer state := by
      change (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    have hidx : state.heap (state.register .address + BitVec.ofNat bits 6) = BitVec.ofNat bits indexBase := by
      rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have ht : Ordinary.targetAddress state pointer = BitVec.ofNat bits (indexBase + (a - C0)) := by
      simp only [Ordinary.targetAddress, hidx, hp, hc, BitVec.ofNat_add_ofNat]
    have hfit : Fits bits (indexBase + (a - C0)) := lt_trans (by omega) hend
    have hpfit : Fits bits point := lt_of_le_of_lt (by omega) hfit
    rw [ConcreteHeap.writeViewHeap, ite_eq_left hg, ht,
      Function.update_of_ne (word_address_ne hpfit hfit (by omega))]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem Data.write_replacement (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : Data q full state.heap) (pointer : Register) (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full) :
    Data q full (ConcreteHeap.writeViewHeap q state pointer) := by
  have hp := SourceRep.pointer_nat q full logical state hrep pointer hptr
  have hc := Data.cutoff_nat q full hq state data hrep.address
  have hi := Data.index_nat q full hq state data hrep.address
  apply Data.of_frame q full hq state.heap _ data
  · intro point hpoint
    exact SourceRep.write_low_frame q (oldCapacity q full) (indexBase q full) (indexWords q full)
      (logical.register pointer) point state pointer hp hc hi had (by unfold indexBase; omega)
      (ordinary_end_fits q full hq) (packed_next q full hq _) hpoint
  · intro offset hoff
    exact SourceRep.write_high_frame q (oldCapacity q full) (PreparedLayout.capacity q full) (indexBase q full) (indexWords q full)
      (logical.register pointer) (controlBase q full + offset) state pointer hp hc hi hq
      (by have hh := bits_room q full; omega) (oldCapacity_le q full hq) had (packed_lookahead_before_end q full)
      (by have hh := ordinary_before_control q full; omega) (bank_offset_fits q full hq offset (by omega))
  · intro point hpoint hfit
    exact SourceRep.write_high_frame q (oldCapacity q full) (PreparedLayout.capacity q full) (indexBase q full) (indexWords q full)
      (logical.register pointer) point state pointer hp hc hi hq
      (by have hh := bits_room q full; omega) (oldCapacity_le q full hq) had (packed_lookahead_before_end q full)
      (by have hh := ordinary_before_control q full; omega) hfit

theorem write_replacement_offset (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : Data q full state.heap) (pointer : Register) (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (offset : Nat) (hoff : offset ≤ 512) :
    ConcreteHeap.writeViewHeap q state pointer (BitVec.ofNat _ (controlBase q full + offset)) =
      state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  exact SourceRep.write_high_frame q (oldCapacity q full) (PreparedLayout.capacity q full) (indexBase q full) (indexWords q full)
    (logical.register pointer) (controlBase q full + offset) state pointer
    (SourceRep.pointer_nat q full logical state hrep pointer hptr) (Data.cutoff_nat q full hq state data hrep.address)
    (Data.index_nat q full hq state data hrep.address) hq (by have hh := bits_room q full; omega)
    (oldCapacity_le q full hq) had (packed_lookahead_before_end q full) (by have hh := ordinary_before_control q full; omega)
    (bank_offset_fits q full hq offset hoff)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
