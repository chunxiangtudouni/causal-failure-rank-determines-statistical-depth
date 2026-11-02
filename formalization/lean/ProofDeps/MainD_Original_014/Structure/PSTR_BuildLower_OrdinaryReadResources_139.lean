module

public import Structure.PSTR_BuildLower_OrdinaryResources_123
public import Structure.PSTR_BuildLower_LoadResources_101

/-! The actual ordinary read uses the SAME old-C0 rebased target geometry
as the frozen writer. Its every prefix is readonly and each primitive load
is allocated; no new original-caller qualification or fetched answer is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.OrdinaryResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034

theorem read_keeps_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ Ordinary.read pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ Ordinary.read pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ Ordinary.read pointer ++ right) state 12 ∧
      PackedAccessSafe (allocated q full) physical (Ordinary.read pointer) state := by
  have target := address_eq_room q full hq pointer logical state hrep data hptr had
  constructor
  · apply ResourceTrace.of_readonly q full physical _ state 12 bounded
    intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state (Ordinary.read_straight pointer) hcode hpcfit hpc ha clock
      (by simpa only [Ordinary.read_length] using hc), Ordinary.read_prefix_heap]
  · intro clock hc
    apply Ordinary.read_access physical pointer state (allocated q full) clock
      (BankAccess.point_room q full hq state hrep.address (registerOffset pointer)
        (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega))
      (BankAccess.point_room q full hq state hrep.address 3 (by decide))
      (BankAccess.point_room q full hq state hrep.address 6 (by decide))
    · rw [target.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt target.2.2.2]
      exact target.2.2.1.trans (lt_of_le_of_lt (by omega) (bank512_room q full))
    · simpa only [Ordinary.read_length] using hc

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.OrdinaryResources
