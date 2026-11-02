module

public import Structure.PSTR_BuildLower_LoopPrefixResources_155
public import Structure.PSTR_BuildLower_LoopSource_077

/-! Actual reversed-range countdown induction transports full NEW-C
capacity and every fitted high-cache word at the SAME endpoint as the
original source/context/environment. Actual prefix certificates are
composed through the same selected cycle and remaining clocks. No machine state or source history is reset. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PrefixCountdown
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (body : Program) (counter depth : Nat)
    (hc : counter < 21) (executable : SourceRep.PrefixExecutable q full used body (depth + 1))
    (environment : Nat → Nat) (shape : ASTShape.Shape body)
    (hdepth : programRepeatDepth body + (depth + 1) ≤ 3) (left right : List PackingOp)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock (64 + counter) left.length
      (lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock (64 + counter) left.length
      (lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)) ++ right).length))
    (count : Nat) (hfit : Fits (bits q full) count)
    (values : ∀ index < count, ExprBounds.allExprNodesFit (bits q full)
      (dimensionROM full.length q (t q full)) (Function.update environment counter (index + 1)) body)
    (logical : State)
    (context : SourceContext.Context q full
      (LoopSource.code (dimensionROM full.length q (t q full)) environment counter body count) logical)
    (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (Function.update environment counter count address))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false) :
    ∃ steps ≤ count * (ASTBudget.budget body (dimensionROM full.length q (t q full)) + 14) + 5,
      let code := lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)
      let after := packingRun (CompactControllerClaims.controllerInput q full used)
        (left ++ relativeLoopBlock (64 + counter) left.length code ++ right) steps state
      SourceRep.Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (LoopSource.code (dimensionROM full.length q (t q full)) environment counter body count) logical) after ∧
      RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + code.length + 14)) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter 0 address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + (depth + 1) ∨ 99 ≤ offset) →
        offset ≠ 64 + counter → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap ∧
      ResourceTrace.Keeps q full (CompactControllerClaims.controllerInput q full used)
        (left ++ relativeLoopBlock (64 + counter) left.length code ++ right) state steps ∧
      TraceAccess.Safe (allocated q full) (CompactControllerClaims.controllerInput q full used)
        (left ++ relativeLoopBlock (64 + counter) left.length code ++ right) state steps := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let code := lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)
  let whole := left ++ relativeLoopBlock (64 + counter) left.length code ++ right
  revert hfit values logical context state hrep data bounded henv hpc ha
  induction count with
  | zero =>
    intro _hfit _values logical _context state hrep data bounded henv hpc ha
    have headPost := LoopData.head_data q full runtime (64 + counter) left code right logical state hrep data hpc ha hcode hpcfit
    have zero : (state.heap (state.register .address + BitVec.ofNat _ (64 + counter))).toNat = 0 := by
      rw [henv counter hc, Function.update_self]
      rfl
    have headKeeps := ControlPrefix.head_keeps q full runtime (64 + counter) left code right state bounded hpc ha hcode hpcfit
    refine ⟨5, by omega, ?_⟩
    dsimp only
    refine ⟨?_, headPost.2.1, ?_, headPost.2.2.2.2.1, ?_, ?_, (headKeeps 5 le_rfl).1, (headKeeps 5 le_rfl).2, headKeeps,
      LoopControlAccess.head q full hq runtime (64 + counter) (by omega) left code right state hrep.address hpc ha hcode hpcfit⟩
    · simpa only [LoopSource.code_zero, IndexedClosureRAM.execute] using headPost.1
    · simpa only [zero, ite_true] using headPost.2.2.2.2.2
    · intro address had
      rw [headPost.2.2.1, headPost.2.2.2.1]
      exact henv address had
    · intro offset ho hout hsave hne
      rw [headPost.2.2.1]
  | succ count ih =>
    intro hfit values logical context state hrep data bounded henv hpc ha
    obtain ⟨cycleCount, cycleBound, cyclePost⟩ := LoopPrefixCycle.run q full used hq hl body counter depth hc executable
      (Function.update environment counter (count + 1)) (by simp only [Function.update_self]; omega)
      (by simpa only [Function.update_self] using hfit) logical
      (LoopSource.iterationContext q full environment counter body count logical context)
      state hrep data bounded shape (values count (by omega)) hdepth henv left right hpc ha hcode hpcfit
    let middle := packingRun runtime whole cycleCount state
    have middleEnv : ∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter count address) := by
      simpa only [Function.update_self, Nat.add_sub_cancel, Function.update_idem] using cyclePost.2.2.2.2.1
    have nextFit : Fits (bits q full) count := by change count < 2 ^ bits q full; change count + 1 < 2 ^ bits q full at hfit; omega
    obtain ⟨remaining, remainingBound, remainingPost⟩ := ih nextFit
      (by intro index hi; exact values index (by omega)) _
      (LoopSource.remainingContext q full environment counter body count logical context)
      middle cyclePost.1 cyclePost.2.1 cyclePost.2.2.2.2.2.2.1 middleEnv cyclePost.2.2.1 cyclePost.2.2.2.1
    have allKeeps := ResourceTrace.keeps_add q full runtime whole state cycleCount remaining
      cyclePost.2.2.2.2.2.2.2.2.1 remainingPost.2.2.2.2.2.2.2.2.1
    have allSafe := TraceAccess.add (allocated q full) runtime whole state cycleCount remaining
      cyclePost.2.2.2.2.2.2.2.2.2 remainingPost.2.2.2.2.2.2.2.2.2
    refine ⟨cycleCount + remaining, ?_, ?_⟩
    · calc
        cycleCount + remaining ≤ (ASTBudget.budget body _ + 14) + (count * (ASTBudget.budget body _ + 14) + 5) := Nat.add_le_add cycleBound remainingBound
        _ = (count + 1) * (ASTBudget.budget body _ + 14) + 5 := by ring
    · dsimp only
      rw [PSTRWordSegments.run_add]
      refine ⟨?_, remainingPost.2.1, remainingPost.2.2.1, remainingPost.2.2.2.1, remainingPost.2.2.2.2.1, ?_,
        remainingPost.2.2.2.2.2.2.1, ?_, allKeeps, allSafe⟩
      · simpa only [LoopSource.execute_succ, middle] using remainingPost.1
      · intro offset ho hout hsave hne
        exact (remainingPost.2.2.2.2.2.1 offset ho hout hsave hne).trans
          (cyclePost.2.2.2.2.2.1 offset ho hout hsave hne)
      · exact ResourceTrace.CacheFrame.trans remainingPost.2.2.2.2.2.2.2.1 cyclePost.2.2.2.2.2.2.2.1

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PrefixCountdown
