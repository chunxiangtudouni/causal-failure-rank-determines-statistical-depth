module

public import Structure.PSTR_BuildLower_OpsPrefixResources_151
public import Structure.PSTR_BuildLower_ASTBudget_081

/-! Endpoint invariant for the actual structured compiler: the SAME
count carries original source/Data/environment and full NEW-C capacity plus
every fitted high-cache word. The code constructor consumes concrete typed
instruction prefix proofs; no raw caller performance/answer oracle is a field. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

def ProgramPrefixRuns (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (program : Program) (depth : Nat) (environment : Nat → Nat) (logical : State)
    (state : WordState (bits q full)) (left right : List PackingOp) : Prop :=
  ∃ count ≤ ASTBudget.budget program (dimensionROM full.length q (t q full)),
    let block := lowerProgram ConcreteAST.ports program left.length depth
    let after := packingRun physical (left ++ block ++ right) count state
    Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (program.eval (dimensionROM full.length q (t q full)) environment) logical) after ∧
      RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (environment address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + depth ∨ 99 ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap ∧
      ResourceTrace.Keeps q full physical (left ++ block ++ right) state count ∧
      TraceAccess.Safe (allocated q full) physical (left ++ block ++ right) state count

def PrefixExecutable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (program : Program) (depth : Nat) : Prop :=
  ∀ (_hq : 0 < q) (_hlaminar : LaminarSchedule full) (environment : Nat → Nat) (logical : State),
    SourceContext.Context q full (program.eval (dimensionROM full.length q (t q full)) environment) logical →
    ∀ (state : WordState (bits q full)), Prepared q full logical state → RuntimeData.Data q full state.heap → GlobalCapacity.Bounded q full state.heap →
      ASTShape.Shape program → ExprBounds.allExprNodesFit (bits q full) (dimensionROM full.length q (t q full)) environment program →
      programRepeatDepth program + depth ≤ 3 →
      (∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address)) →
      ∀ (left right : List PackingOp), state.pc = BitVec.ofNat _ (5 * left.length) → state.halted = false →
        WordsFit (bits q full) (packingCode (left ++ lowerProgram ConcreteAST.ports program left.length depth ++ right)) →
        Fits (bits q full) (5 * (left ++ lowerProgram ConcreteAST.ports program left.length depth ++ right).length) →
        ProgramPrefixRuns q full (CompactControllerClaims.controllerInput q full used) program depth environment logical state left right

theorem code_prefix_executable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (ops : List OpExpr) (depth : Nat) : PrefixExecutable q full used (.code ops) depth := by
  intro hq hlaminar environment logical context state hrep data bounded hshape hvalues hdepth henv left right hpc ha hcode hpcfit
  obtain ⟨count, hcount, result⟩ := ops_prefix_resources q full used hq hlaminar ops environment logical context state hrep data bounded
    hshape (by intro op hm; exact hvalues op hm) henv left right hpc ha hcode hpcfit
  refine ⟨count, hcount, ?_⟩
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1, result.2.2.2.2.1,
    (by intro offset ho hout hsave; exact result.2.2.2.2.2.1 offset ho hout),
    result.2.2.2.2.2.2.1, result.2.2.2.2.2.2.2.1,
    result.2.2.2.2.2.2.2.2.1, result.2.2.2.2.2.2.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
