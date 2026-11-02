module

public import Structure.PSTR_BuildLower_ProgramPrefixResources_152

/-! SAME-program append composes source/Data/environment and every-prefix certificates,
full NEW-C capacity and every fitted high-cache word. The actual left
endpoint supplies the right input; count/source context/heap are not reset. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem append_prefix_executable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (first second : Program) (depth : Nat)
    (firstPrefixExecutable : PrefixExecutable q full used first depth)
    (secondPrefixExecutable : PrefixExecutable q full used second depth) : PrefixExecutable q full used (.append first second) depth := by
  intro hq hlaminar environment logical context state hrep data bounded hshape hvalues hdepth henv left right hpc ha hcode hpcfit
  let rom := dimensionROM full.length q (t q full)
  let runtime := CompactControllerClaims.controllerInput q full used
  let firstCode := lowerProgram ConcreteAST.ports first left.length depth
  let secondCode := lowerProgram ConcreteAST.ports second (left.length + firstCode.length) depth
  have sourceContext : SourceContext.Context q full (first.eval rom environment ++ second.eval rom environment) logical := context
  have firstDepth : programRepeatDepth first + depth ≤ 3 := by
    change max (programRepeatDepth first) (programRepeatDepth second) + depth ≤ 3 at hdepth
    have hh := Nat.le_max_left (programRepeatDepth first) (programRepeatDepth second)
    omega
  have secondDepth : programRepeatDepth second + depth ≤ 3 := by
    change max (programRepeatDepth first) (programRepeatDepth second) + depth ≤ 3 at hdepth
    have hh := Nat.le_max_right (programRepeatDepth first) (programRepeatDepth second)
    omega
  obtain ⟨firstCount, firstBound, firstResult⟩ := firstPrefixExecutable hq hlaminar environment logical
    (SourceContext.left sourceContext) state hrep data bounded hshape.1 hvalues.1 firstDepth henv
    left (secondCode ++ right) hpc ha
    (by simpa only [lowerProgram, List.append_assoc, firstCode, secondCode] using hcode)
    (by simpa only [lowerProgram, List.append_assoc, firstCode, secondCode] using hpcfit)
  let middle := packingRun runtime (left ++ firstCode ++ secondCode ++ right) firstCount state
  have firstResult' : Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic (first.eval rom environment) logical) middle ∧
      RuntimeData.Data q full middle.heap ∧ middle.pc = BitVec.ofNat _ (5 * (left.length + firstCode.length)) ∧ middle.halted = false ∧
      (∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + depth ∨ 99 ≤ offset) →
        middle.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full middle.heap ∧ ResourceTrace.CacheFrame q full state.heap middle.heap ∧
      ResourceTrace.Keeps q full runtime (left ++ firstCode ++ secondCode ++ right) state firstCount ∧
      TraceAccess.Safe (allocated q full) runtime (left ++ firstCode ++ secondCode ++ right) state firstCount := by
    simpa only [List.append_assoc, firstCode, middle, rom] using firstResult
  obtain ⟨lastCount, lastBound, lastResult⟩ := secondPrefixExecutable hq hlaminar environment _
    (SourceContext.right sourceContext) middle firstResult'.1 firstResult'.2.1 firstResult'.2.2.2.2.2.2.1 hshape.2 hvalues.2 secondDepth
    firstResult'.2.2.2.2.1 (left ++ firstCode) right
    (by simpa only [List.length_append] using firstResult'.2.2.1) firstResult'.2.2.2.1
    (by simpa only [lowerProgram, List.append_assoc, List.length_append, firstCode, secondCode] using hcode)
    (by simpa only [lowerProgram, List.append_assoc, List.length_append, firstCode, secondCode] using hpcfit)
  have last := lastResult
  simp only [List.length_append, List.append_assoc] at last
  refine ⟨firstCount + lastCount, ?_, ?_⟩
  · change firstCount + lastCount ≤ ASTBudget.budget first _ + ASTBudget.budget second _
    omega
  · dsimp only
    simp only [lowerProgram, List.append_assoc, PSTRWordSegments.run_add]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Program.eval, IndexedClosureRAM.execute_append, middle, firstCode, secondCode, rom,
        List.append_assoc] using last.1
    · simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.1
    · simpa only [List.length_append, Nat.add_assoc, middle, firstCode, secondCode, List.append_assoc] using last.2.2.1
    · simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.2.2.1
    · simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.2.2.2.1
    · intro offset ho hout hsave
      have hh := (last.2.2.2.2.2.1 offset ho hout hsave).trans (firstResult'.2.2.2.2.2.1 offset ho hout hsave)
      simpa only [middle, firstCode, secondCode, List.append_assoc] using hh
    · simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.2.2.2.2.2.1
    · have frame := ResourceTrace.CacheFrame.trans last.2.2.2.2.2.2.2.1 firstResult'.2.2.2.2.2.2.2.1
      simpa only [middle, firstCode, secondCode, List.append_assoc] using frame
    · have back : ResourceTrace.Keeps q full runtime (left ++ firstCode ++ secondCode ++ right) middle lastCount := by
        simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.2.2.2.2.2.2.2.1
      have allKeeps := ResourceTrace.keeps_add q full runtime (left ++ firstCode ++ secondCode ++ right) state firstCount lastCount
        firstResult'.2.2.2.2.2.2.2.2.1 back
      simpa only [lowerProgram, middle, firstCode, secondCode, List.append_assoc] using allKeeps
    · have back : TraceAccess.Safe (allocated q full) runtime (left ++ firstCode ++ secondCode ++ right) middle lastCount := by
        simpa only [middle, firstCode, secondCode, List.append_assoc] using last.2.2.2.2.2.2.2.2.2
      have allSafe := TraceAccess.add (allocated q full) runtime (left ++ firstCode ++ secondCode ++ right) state firstCount lastCount
        firstResult'.2.2.2.2.2.2.2.2.2 back
      simpa only [lowerProgram, middle, firstCode, secondCode, List.append_assoc] using allSafe

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
