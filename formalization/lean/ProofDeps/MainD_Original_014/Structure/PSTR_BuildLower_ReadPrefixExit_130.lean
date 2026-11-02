module

public import Structure.PSTR_BuildLower_ReadExit_066
public import Structure.PSTR_BuildLower_TraceAccess_119
public import Structure.PSTR_BuildLower_LoadResources_101

/-! Prefix extension of the EXISTING actual ReadExit. Concrete constructors
must prove frame/access at that SAME steps field. No independent endpoint
witness, supplied answer or original-caller performance premise is added. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

structure ReadPrefixExit {bits : Nat} (heapWords : Nat) (physical : PhysicalROM)
    (left block right : List PackingOp) (state : WordState bits) (value limit : Nat)
    extends ReadExit physical left block right state value limit where
  readonly : ∀ clock ≤ steps, (packingRun physical (left ++ block ++ right) clock state).heap = state.heap
  safe : TraceAccess.Safe heapWords physical (left ++ block ++ right) state steps

theorem ReadPrefixExit.keeps (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (left block right : List PackingOp) (state : WordState (bits q full)) (value limit : Nat)
    (port : ReadPrefixExit (allocated q full) physical left block right state value limit)
    (bounded : GlobalCapacity.Bounded q full state.heap) :
    ResourceTrace.Keeps q full physical (left ++ block ++ right) state port.steps :=
  ResourceTrace.of_readonly q full physical _ state port.steps bounded port.readonly

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
