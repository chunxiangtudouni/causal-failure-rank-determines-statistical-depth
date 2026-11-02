module

public import Structure.PSTR_BuildLower_WholeASTEndResources_112
public import Structure.PSTR_BuildLower_CounterEntry_097

/-! Real64counter-clear plus the fixed fullBuild AST has ONE actual
witness with original source/Data, full NEW-C capacity and every fitted
high-cache endpoint word. No lexical-zero caller premise is exposed.
Original raw producer, whole-prefix access/Fits/cost and HALT remain open. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BuilderEndRun
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17ProgramTemplates041

private theorem builder_pc_length (wordBits : Nat) (left : List PackingOp) (body : Nat → List PackingOp) :
    BitVec.ofNat wordBits (5 * ((left ++ CounterInit.code).length + (body (left ++ CounterInit.code).length).length)) =
      BitVec.ofNat wordBits (5 * (left.length + (CounterInit.code ++ body (left.length + 64)).length)) := by
  apply congrArg (BitVec.ofNat wordBits)
  simp only [List.length_append, CounterInit.code_length]
  omega

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
      ResourceTrace.Keeps q full (CompactControllerClaims.controllerInput q full used) whole state 64 := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let whole := left ++ CounterInit.builderCode left.length ++ right
  let body := lowerProgram ConcreteAST.ports fullBuild (left.length + 64) 0
  let bodyLeft := left ++ CounterInit.code
  have first := CounterEntry.run q full hq runtime (initial (fun _ => 0)) state hrep data bounded left (body ++ right) hpc ha
    (by simpa only [CounterInit.builderCode, List.append_assoc, body] using hcode)
    (by simpa only [CounterInit.builderCode, List.append_assoc, body] using hpcfit)
  let middle := packingRun runtime whole 64 state
  have firstPost : SourceRep.Prepared q full (initial (fun _ => 0)) middle ∧ RuntimeData.Data q full middle.heap ∧
      GlobalCapacity.Bounded q full middle.heap ∧
      (∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) = 0) ∧
      middle.pc = BitVec.ofNat _ (5 * (left.length + 64)) ∧ middle.halted = false ∧
      ResourceTrace.Keeps q full runtime whole state 64 := by
    simpa only [middle, whole, CounterInit.builderCode, List.append_assoc, body] using first
  obtain ⟨bodyCount, bodyBound, bodyPost⟩ := SourceRep.fullBuild_end_run_work q full used hq hl middle
    firstPost.1 firstPost.2.1 firstPost.2.2.1 firstPost.2.2.2.1 bodyLeft right
    (by simpa only [bodyLeft, List.length_append, CounterInit.code_length] using firstPost.2.2.2.2.1)
    firstPost.2.2.2.2.2.1
    (by simpa only [bodyLeft, CounterInit.builderCode, List.length_append, CounterInit.code_length, List.append_assoc] using hcode)
    (by simpa only [bodyLeft, CounterInit.builderCode, List.length_append, CounterInit.code_length, List.append_assoc] using hpcfit)
  have actualProgram : bodyLeft ++ lowerProgram ConcreteAST.ports fullBuild bodyLeft.length 0 ++ right = whole := by
    simp only [bodyLeft, whole, CounterInit.builderCode, List.length_append, CounterInit.code_length, List.append_assoc]
  dsimp only at bodyPost
  rw [actualProgram] at bodyPost
  refine ⟨64 + bodyCount, by omega, ?_⟩
  dsimp only
  rw [PSTRWordSegments.run_add]
  refine ⟨bodyPost.1, bodyPost.2.1, ?_, bodyPost.2.2.2.1, bodyPost.2.2.2.2.1, ?_, firstPost.2.2.2.2.2.2⟩
  · calc
      _ = BitVec.ofNat _ (5 * (bodyLeft.length + (lowerProgram ConcreteAST.ports fullBuild bodyLeft.length 0).length)) := bodyPost.2.2.1
      _ = BitVec.ofNat _ (5 * (left.length + (CounterInit.builderCode left.length).length)) :=
        builder_pc_length (bits q full) left (fun start => lowerProgram ConcreteAST.ports fullBuild start 0)
  · exact ResourceTrace.CacheFrame.trans bodyPost.2.2.2.2.2 (firstPost.2.2.2.2.2.2 64 le_rfl).2

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BuilderEndRun
