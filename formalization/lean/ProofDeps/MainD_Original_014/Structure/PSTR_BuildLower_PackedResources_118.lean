module

public import Structure.PSTR_BuildLower_StoreCapacity_095
public import Structure.PSTR_BuildLower_PackedPointFrame_098
public import Structure.PSTR_BuildLower_AccessBridge_116

/-! The actual packed writer's transient clear/fill states retain the FULL
new capacity and high raw cache. This consumes A06's real72 prefix theorem,
not the smaller finite C0 view or an endpoint-only replacement theorem. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)

theorem write_keeps_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (packed : logical.register pointer < oldCapacity q full) (hvalue : (state.register .value).toNat ≤ q)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode
      (left ++ PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer) ++ right)))
    (hpcfit : Fits (bits q full) (5 *
      (left ++ PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer) ++ right).length)) :
    ResourceTrace.Keeps q full physical
      (left ++ PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer) ++ right) state 72 ∧
    PackedAccessSafe (allocated q full) physical
      (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) state := by
  have hp : (PA06A19PrepareBankPacked021.pointer (registerOffset pointer) state).toNat = logical.register pointer :=
    SourceRep.pointer_nat q full logical state hrep pointer hptr
  have hb : 0 < bits q full := by have hh := bits_room q full; omega
  have baseNat : (state.register .address).toNat = controlBase q full := by
    have hf : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using bank_offset_fits q full hq 0 (by decide)
    rw [hrep.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  have hslot := registerSlot_bounds pointer
  change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hslot
  have widthPositive : 0 < CapacityBits.width q := by
    by_contra hn
    have hz : CapacityBits.width q = 0 := by omega
    have hqz := (CapacityBits.width_eq_zero_iff q).mp hz
    omega
  have lowBound : logical.register pointer * CapacityBits.width q / bits q full <
      packedCapacityWords q (capacity q full) (bits q full) :=
    (Nat.div_lt_iff_lt_mul hb).mpr
      ((Nat.mul_lt_mul_of_pos_right (packed.trans_le (oldCapacity_le q full hq)) widthPositive).trans_le
        (packedCapacityWords_mul_bits q (capacity q full) hb))
  have hnext : Fits (bits q full) ((PA06A19PrepareBankPacked021.pointer (registerOffset pointer) state).toNat *
      CapacityBits.width q / bits q full + 4 + 1) := by
    rw [hp]
    exact packed_next q full hq _ packed
  have hscale : Fits (bits q full) ((PA06A19PrepareBankPacked021.pointer (registerOffset pointer) state).toNat *
      CapacityBits.width q) := by
    rw [hp]
    exact packed_scale q full hq _ packed
  have bankLower : 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤
      (state.register .address).toNat + registerOffset pointer := by
    rw [baseNat]
    have hlo := packed_lookahead_before_end q full
    have hhi := ordinary_before_control q full
    change 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤ _ at hlo
    omega
  have bankFit : Fits (bits q full) ((state.register .address).toNat + registerOffset pointer) := by
    rw [baseNat]
    exact bank_offset_fits q full hq _ (by omega)
  have pointerBound : (PA06A19PrepareBankPacked021.pointer (registerOffset pointer) state).toNat < capacity q full := by
    rw [hp]
    exact packed.trans_le (oldCapacity_le q full hq)
  have region := capacity_product_fits q full hq
  have packedBound : CapacityPrefixBounded q (capacity q full)
      (unpackHeap q (capacity q full) (bits q full) (dataHeap state.heap)) := by
    simpa only [GlobalCapacity.Bounded, CompactControllerClaims.logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using bounded
  constructor
  · intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state
      (PA06A19PrepareBankPacked021.safeWrite_straight _) hcode hpcfit hpc ha clock
      (by simpa only [PA06A19PrepareBankPacked021.safeWrite_length] using hc)]
    constructor
    · simpa only [GlobalCapacity.Bounded, CompactControllerClaims.logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using
        PA06A19PrepareBankPacked021.safeWrite_prefix_capacityBounded q (capacity q full) (registerOffset pointer)
          physical state data.header hq hb (width_room q full) pointerBound hscale hnext bankLower bankFit region hvalue packedBound clock hc
    · intro point above pointFit
      apply PackedPointFrame.prefix_frame q (capacity q full) (registerOffset pointer) physical state data.header hq hb
        (width_room q full) pointerBound hscale hnext bankLower bankFit point pointFit _ clock hc
      rw [hp]
      have hlo := packed_lookahead_before_end q full
      have hhi := ordinary_before_control q full
      change 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤ _ at hlo
      omega
  · refine PA06A19PrepareBankPacked021.safeWrite_accessSafe q (capacity q full) (registerOffset pointer)
      (allocated q full) physical state data.header hq (by have hh := bits_room q full; omega)
      (width_room q full) pointerBound hscale hnext ?_ bankLower bankFit ?_
    · rw [hp]
      have hlo := packed_lookahead_before_end q full
      have hhi := ordinary_before_control q full
      have hall := bank512_room q full
      change 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤ _ at hlo
      omega
    · rw [baseNat]
      exact lt_of_le_of_lt (by omega) (bank512_room q full)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedResources
