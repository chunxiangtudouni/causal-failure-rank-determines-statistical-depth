module

public import Structure.PSTR_BuildLower_InternalAccess_127
public import Structure.PSTR_BuildLower_LoadResources_101
public import Structure.PSTR_BuildLower_FixedExprAccess_115

/-! True25-clock internal-cache getter: SAME containing run, readonly full
Cnew/high-cache prefixes and actual fetch/decode/access. Every local address
is discharged from produced words and original common allocation geometry. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034

theorem actual_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (a : Nat) (hp : (Ordinary.pointerValue state pointer).toNat = a) (hupper : a < 2 * t q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ InternalInput.code pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ InternalInput.code pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ InternalInput.code pointer ++ right) state 25 ∧
      TraceAccess.Safe (allocated q full) physical (left ++ InternalInput.code pointer ++ right) state 25 := by
  have massRoomNat : controlBase q full + 528 < allocated q full := by
    unfold controlBase allocated
    omega
  have massRoom : (state.register .address + BitVec.ofNat _ 528).toNat < allocated q full := by
    rw [base, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (massRoomNat.trans (allocation_fits q full hq))]
    exact massRoomNat
  have primitive : PackedAccessSafe (allocated q full) physical (InternalInput.code pointer) state :=
    local_safe physical pointer (allocated q full) state
      (BankAccess.point_room q full hq state base (registerOffset pointer)
        (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega))
      massRoom (BankAccess.point_room q full hq state base 2 (by decide))
      (target_room q full hq pointer state base data a hp hupper)
  constructor
  · apply ResourceTrace.of_readonly q full physical _ state 25 bounded
    intro clock hc
    rw [SourceRep.straight_prefix physical left _ right state (InternalInput.code_straight pointer) hcode hpcfit hpc ha clock
      (by simpa only [InternalInput.code_length] using hc)]
    exact (InternalInput.prefix_frame physical pointer state clock).1
  · have result := TraceAccess.straight physical left (InternalInput.code pointer) right (allocated q full) state
      (InternalInput.code_straight pointer) primitive hpc ha hcode hpcfit
    simpa only [InternalInput.code_length] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalAccess
