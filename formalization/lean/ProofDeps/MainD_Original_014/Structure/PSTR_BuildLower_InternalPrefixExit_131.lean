module

public import Structure.PSTR_BuildLower_ReadPrefixExit_130
public import Structure.PSTR_BuildLower_ConcreteReadExits_067
public import Structure.PSTR_BuildLower_InternalResources_128

/-! The original actual internal ReadExit has steps=25 by construction.
Its SAME count receives the true fetched-prefix heap/access certificates;
no equality of separately selected run witnesses is assumed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

def internal_read_prefix_exit (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer)) (hupper : logical.register pointer < 2 * t q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ InternalInput.code pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ InternalInput.code pointer ++ right).length)) :
    ReadPrefixExit (allocated q full) physical left (InternalInput.code pointer) right state
      ((givenTreeROM q full).semantic.read .internal (logical.register pointer)) 25 := by
  let baseExit := internal_read_exit q full physical pointer logical state hrep data hptr hupper left right hpc ha hcode hpcfit
  have resources := InternalAccess.actual_resources q full hq physical pointer state hrep.address data bounded
    (logical.register pointer) (pointer_nat q full logical state hrep pointer hptr) hupper left right hpc ha hcode hpcfit
  refine { toReadExit := baseExit, readonly := ?_, safe := ?_ }
  · intro clock hc
    change clock ≤ 25 at hc
    rw [straight_prefix physical left _ right state (InternalInput.code_straight pointer) hcode hpcfit hpc ha clock
      (by simpa only [InternalInput.code_length] using hc)]
    exact (InternalInput.prefix_frame physical pointer state clock).1
  · change TraceAccess.Safe (allocated q full) physical (left ++ InternalInput.code pointer ++ right) state 25
    exact resources.2

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
