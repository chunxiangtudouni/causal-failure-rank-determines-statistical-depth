module

public import Structure.PSTR_BuildLower_AppendEndResources_108
public import Structure.PSTR_BuildLower_RepeatEndResources_111
public import Structure.PSTR_BuildLower_BudgetWork_087

/-! Whole fixed typed AST with ONE actual witness carrying source/Data,
full NEW-C capacity and every fitted high-cache endpoint word. All body
contracts are discharged structurally. True producer entry, whole-prefix
access/Fits, original charged totalCost and global HALT are still separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem program_end_executable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (program : Program) (depth : Nat) : EndExecutable q full used program depth := by
  induction program generalizing depth with
  | code ops => exact code_end_executable q full used ops depth
  | append first second ihFirst ihSecond =>
    exact append_end_executable q full used first second depth (ihFirst depth) (ihSecond depth)
  | «repeat» counter bound body ih =>
    exact repeat_end_executable q full used counter bound body depth (ih (depth + 1))

theorem fullBuild_end_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (bits q full)) (hrep : Prepared q full (initial (fun _ => 0)) state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = 0)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerProgram ConcreteAST.ports fullBuild left.length 0 ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerProgram ConcreteAST.ports fullBuild left.length 0 ++ right).length)) :
    ProgramEndRuns q full (CompactControllerClaims.controllerInput q full used) fullBuild 0 (fun _ => 0)
      (initial (fun _ => 0)) state left right := by
  apply program_end_executable q full used fullBuild 0 hq hl (fun _ => 0) (initial (fun _ => 0))
    _ state hrep data bounded ASTShape.fullBuild_shape (ExprBounds.prepared_fullBuild_initial_nodesFit q full)
    (by decide) henv left right hpc ha hcode hpcfit
  simpa only [fullBuild_eval] using SourceContext.start q full

theorem fullBuild_end_run_work (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (bits q full)) (hrep : Prepared q full (initial (fun _ => 0)) state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = 0)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerProgram ConcreteAST.ports fullBuild left.length 0 ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerProgram ConcreteAST.ports fullBuild left.length 0 ++ right).length)) :
    ∃ count ≤ (ASTBudget.factor fullBuild * 32768) * work full.length q (t q full),
      let block := lowerProgram ConcreteAST.ports fullBuild left.length 0
      let after := packingRun (CompactControllerClaims.controllerInput q full used) (left ++ block ++ right) count state
      Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (PA17TableBuild005.buildProgram full.length q (t q full)) (initial (fun _ => 0))) after ∧
      RuntimeData.Data q full after.heap ∧ after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap := by
  obtain ⟨count, bound, post⟩ := fullBuild_end_run q full used hq hl state hrep data bounded henv left right hpc ha hcode hpcfit
  refine ⟨count, bound.trans (ASTBudget.fullBuild_budget_work q full hq hl (fun _ => 0)), ?_⟩
  exact ⟨by simpa only [fullBuild_eval] using post.1, post.2.1, post.2.2.1, post.2.2.2.1,
    post.2.2.2.2.2.2.1, post.2.2.2.2.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
