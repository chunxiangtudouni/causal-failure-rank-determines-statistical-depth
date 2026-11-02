module

public import Structure.PA06_A19Prepare_PostDP055_Data

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same-clock builder wrapper. The frozen113 theorem provides
one count for the real64-op counter initializer and fullBuild body. Only
those first64 clocks have Keeps here; no whole-AST safety is asserted. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims

def builderClockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  64 + (PSTRBuildLower.ASTBudget.factor PA17ProgramTemplates041.fullBuild * 32768) *
    work full.length q (PSTRBuildLower.PreparedLayout.t q full)

theorem builder_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (indexWidth 32 full.length q))
    (pre : PA06A19PreparePreBuild044.Data q full before)
    (raw : PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (left right : List PackingOp)
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right)))
    (hpcfit : Fits (indexWidth 32 full.length q)
      (5 * (left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right).length)) :
    ∃ count ≤ builderClockBound q full,
      let code := left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right
      let after := packingRun (controllerInput q full used) code count before
      Data q full after ∧
        after.pc = BitVec.ofNat _
          (5 * (left.length + (PSTRBuildLower.CounterInit.builderCode left.length).length)) ∧
        after.halted = false ∧
        PSTRBuildLower.ResourceTrace.CacheFrame q full before.heap after.heap ∧
        PSTRBuildLower.ResourceTrace.Keeps q full (controllerInput q full used) code before 64 := by
  have entry := PA06A19PrepareSTInput050.st_input_of_data q full hq before pre
  obtain ⟨count, bound, post⟩ := PSTRBuildLower.BuilderEndRun.run q full used hq hl
    before entry.2.1 entry.1 entry.2.2 left right hpc ha hcode hpcfit
  dsimp only at post
  rcases post with ⟨source, runtime, pc, active, bounded, frame, first64⟩
  refine ⟨count, bound, ?_⟩
  dsimp only
  exact ⟨data_of_builder_outputs q full hq hl before _ pre raw source runtime bounded frame,
    pc, active, frame, first64⟩

end PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055
