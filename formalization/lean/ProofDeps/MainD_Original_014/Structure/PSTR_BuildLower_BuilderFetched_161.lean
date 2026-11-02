module

public import Structure.PSTR_BuildLower_BuilderPrefixResources_160
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix

/-! Exact A06 consumer vocabulary for the SAME strong-builder witness.
Fetched and TraceAccess.Safe have the identical actual state/PC/decode/access
fields. No additional run, count identification or caller oracle is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BuilderFetchedRun
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17ProgramTemplates041

theorem safe_iff_fetched {wordBits : Nat} (H : Nat) (rom : PhysicalROM) (code : List PackingOp)
    (state : WordState wordBits) (count : Nat) :
    TraceAccess.Safe H rom code state count ↔
      ∀ clock < count, PA06A19PrepareInitialUsed037.Fetched H rom code (packingRun rom code clock state) := Iff.rfl

theorem run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full (initial (fun _ => 0)) state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ CounterInit.builderCode left.length ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ CounterInit.builderCode left.length ++ right).length)) :
    ∃ count ≤ 64 + (ASTBudget.factor fullBuild * 32768) * work full.length q (t q full),
      let whole := left ++ CounterInit.builderCode left.length ++ right
      let after := packingRun (CompactControllerClaims.controllerInput q full used) whole count state
      SourceRep.Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (PA17TableBuild005.buildProgram full.length q (t q full)) (initial (fun _ => 0))) after ∧
      RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + (CounterInit.builderCode left.length).length)) ∧ after.halted = false ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap ∧
      ∀ clock < count, PA06A19PrepareInitialUsed037.Fetched (allocated q full)
        (CompactControllerClaims.controllerInput q full used) whole
        (packingRun (CompactControllerClaims.controllerInput q full used) whole clock state) := by
  obtain ⟨count, bound, post⟩ := BuilderPrefixRun.run q full used hq hl state hrep data bounded left right hpc ha hcode hpcfit
  refine ⟨count, bound, post.1, post.2.1, post.2.2.1, post.2.2.2.1, post.2.2.2.2.1, post.2.2.2.2.2.1, ?_⟩
  exact (safe_iff_fetched _ _ _ state count).mp post.2.2.2.2.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BuilderFetchedRun
