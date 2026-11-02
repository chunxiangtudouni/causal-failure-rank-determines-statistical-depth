module

public import Structure.PSTR_BuildLower_BuilderEndResources_113

/-! The real fullAST source endpoint already contains the original table.
Transport uses the proved finite C0 view and original DP correctness only;
NEW-C physical decoding is matched by the existing exact two-cutoff lemma. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open CompactControllerClaims (dataHeap)

theorem table_endpoint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (bits q full))
    (hrep : Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (PA17TableBuild005.buildProgram full.length q (t q full)) (initial (fun _ => 0))) state) :
    PhysicalTableCorrect q full (CompactControllerClaims.logicalHeap q (capacity q full) state.heap) := by
  let source := IndexedClosureRAM.execute (givenTreeROM q full).semantic
    (PA17TableBuild005.buildProgram full.length q (t q full)) (initial (fun _ => 0))
  have sourceCorrect : PhysicalTableCorrect q full source.heap :=
    (PA17TableBuild005.prepared_build_correct q full hq hl).1
  have tableBound : tableWords full.length q (t q full) ≤ oldCapacity q full :=
    PA06A19PreparePackedView013.tableWords_le_oldCapacity _ _ _
  have viewCorrect : PhysicalTableCorrect q full
      (PA06A19PreparePackedView013.view q (oldCapacity q full) (capacity q full) (indexBase q full) state.heap) := by
    apply (PA06A19PreparePackedView013.physicalTableCorrect_congr_prefix q full _ source.heap ?_).mpr sourceCorrect
    intro address had
    change address < tableWords full.length q (t q full) at had
    exact hrep.heap address (by omega)
  have actual : PhysicalTableCorrect q full (unpackHeap q (capacity q full) (bits q full) (dataHeap state.heap)) :=
    (PA06A19PreparePackedView013.physicalTableCorrect_view_iff q full (capacity q full) (indexBase q full) state.heap).mp viewCorrect
  simpa only [CompactControllerClaims.logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using actual

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
