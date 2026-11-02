module

public import Structure.PSTR_BuildLower_PackedReadAccess_141
public import Structure.PSTR_BuildLower_LoadResources_101
public import Structure.PSTR_BuildLower_PreparedPortRoom_060
public import Structure.PSTR_BuildLower_RuntimeData_062

/-! Actual21-op packed reader prefixes: fullCnew and all fitted high-cache
words stay unchanged, and every primitive read is allocated. Pointer/room
facts come from original dimensions and the true preloaded old register. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedReadResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034 AlgorithmClaims.PackedCapacityRAM

theorem read_keeps_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (state : WordState (bits q full))
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (a : Nat) (hold : (state.register .old).toNat = a) (ha : a < oldCapacity q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (hactive : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ PA06A19PrepareBankPacked021.read ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ PA06A19PrepareBankPacked021.read ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ PA06A19PrepareBankPacked021.read ++ right) state 21 ∧
      PackedAccessSafe (allocated q full) physical PA06A19PrepareBankPacked021.read state := by
  have hb : 0 < bits q full := by have hh := bits_room q full; omega
  have widthPositive : 0 < CapacityBits.width q := by
    by_contra hn
    have hz : CapacityBits.width q = 0 := by omega
    have hqz := (CapacityBits.width_eq_zero_iff q).mp hz
    omega
  have lowBound : a * CapacityBits.width q / bits q full < packedCapacityWords q (capacity q full) (bits q full) :=
    (Nat.div_lt_iff_lt_mul hb).mpr
      ((Nat.mul_lt_mul_of_pos_right (ha.trans_le (oldCapacity_le q full hq)) widthPositive).trans_le
        (packedCapacityWords_mul_bits q (capacity q full) hb))
  have hs : Fits (bits q full) ((state.register .old).toNat * CapacityBits.width q) := by
    rw [hold]
    exact packed_scale q full hq a ha
  have hf : Fits (bits q full) (4 + ((state.register .old).toNat * CapacityBits.width q / bits q full + 1)) := by
    rw [hold]
    have existing := packed_next q full hq a ha
    exact lt_of_le_of_lt (by omega) existing
  have hl : 4 + ((state.register .old).toNat * CapacityBits.width q / bits q full + 1) < allocated q full := by
    rw [hold]
    have packedEnd := packed_lookahead_before_end q full
    change 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤ _ at packedEnd
    have ordinaryEnd := ordinary_before_control q full
    have controlEnd := bank512_room q full
    omega
  constructor
  · apply ResourceTrace.of_readonly q full physical _ state 21 bounded
    intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state PA06A19PrepareBankPacked021.read_straight
      hcode hpcfit hpc hactive clock (by simpa only [PA06A19PrepareBankPacked021.read_length] using hc)]
    rw [PA06A19PrepareBankPacked021.read_prefix_simulation physical state clock hc]
    exact PA06A19PrepareRuntimePacked016.read_prefix_heap physical
      (PA06A19PrepareBankPacked021.withAddress (state.register .old) state) clock
  · exact PackedReadAccess.local_safe q (allocated q full) physical state data.header
      (by have hh := bits_room q full; omega) (width_room q full) hs hf hl

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedReadResources
