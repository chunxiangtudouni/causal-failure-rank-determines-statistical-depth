module

public import Structure.PSTR_BuildLower_StoreCapacity_095
public import Structure.PSTR_BuildLower_FixedExprAccess_115

/-! The ordinary side of the real old-C0 dispatcher is rebased into the
finite NEW physical ordinary domain. Actual prefix frames carry full Cnew
and high cache, while actual load/store accesses stay in the old allocation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.OrdinaryResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034

theorem address_eq_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full) :
    let point := indexBase q full + (logical.register pointer - oldCapacity q full)
    Ordinary.targetAddress state pointer = BitVec.ofNat _ point ∧ indexBase q full ≤ point ∧
      point < controlBase q full ∧ Fits (bits q full) point := by
  have hp := SourceRep.pointer_nat q full logical state hrep pointer hptr
  have hc := RuntimeData.Data.cutoff_nat q full hq state data hrep.address
  have hi := RuntimeData.Data.index_nat q full hq state data hrep.address
  have indexWord : state.heap (state.register .address + BitVec.ofNat _ 6) = BitVec.ofNat _ (indexBase q full) := by
    rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ht : Ordinary.targetAddress state pointer =
      BitVec.ofNat _ (indexBase q full + (logical.register pointer - oldCapacity q full)) := by
    simp only [Ordinary.targetAddress, hp, hc, indexWord, BitVec.ofNat_add_ofNat]
  have indexPositive : 0 < indexWords q full := by unfold indexWords; omega
  have endBound : indexBase q full + (logical.register pointer - oldCapacity q full) <
      indexBase q full + indexWords q full := by omega
  exact ⟨ht, by omega, endBound.trans_le (ordinary_before_control q full),
    endBound.trans (ordinary_end_fits q full hq)⟩

theorem write_keeps_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ Ordinary.write pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ Ordinary.write pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ Ordinary.write pointer ++ right) state 12 ∧
      PackedAccessSafe (allocated q full) physical (Ordinary.write pointer) state := by
  let point := indexBase q full + (logical.register pointer - oldCapacity q full)
  have target := address_eq_room q full hq pointer logical state hrep data hptr had
  have frame (clock : Nat) (address : Nat) (hf : Fits (bits q full) address) (hne : address ≠ point) :
      (executeOps physical ((Ordinary.write pointer).take clock) state).heap (BitVec.ofNat _ address) =
        state.heap (BitVec.ofNat _ address) := by
    apply Ordinary.write_prefix_frame
    rw [target.1]
    exact word_address_ne hf target.2.2.2 hne
  constructor
  · intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state (Ordinary.write_straight pointer) hcode hpcfit hpc ha clock
      (by simpa only [Ordinary.write_length] using hc)]
    constructor
    · apply GlobalCapacity.of_packed_frame q full hq state.heap _ bounded
      intro address hadr
      apply frame clock address
      · exact lt_of_lt_of_le hadr (lt_of_le_of_lt target.2.1 target.2.2.2).le
      · change address ≠ indexBase q full + (logical.register pointer - oldCapacity q full)
        omega
    · intro address hadr hf
      apply frame clock address hf
      change address ≠ indexBase q full + (logical.register pointer - oldCapacity q full)
      have upper := target.2.2.1
      omega
  · intro clock hc
    apply Ordinary.write_access physical pointer state (allocated q full) clock
      (BankAccess.point_room q full hq state hrep.address (registerOffset pointer)
        (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega))
      (BankAccess.point_room q full hq state hrep.address 3 (by decide))
      (BankAccess.point_room q full hq state hrep.address 6 (by decide))
    · rw [target.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt target.2.2.2]
      exact target.2.2.1.trans (lt_of_le_of_lt (by omega) (bank512_room q full))
    · simpa only [Ordinary.write_length] using hc

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.OrdinaryResources
