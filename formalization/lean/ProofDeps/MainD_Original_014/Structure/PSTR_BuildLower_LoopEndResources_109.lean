module

public import Structure.PSTR_BuildLower_ProgramEndResources_107
public import Structure.PSTR_BuildLower_ControlPrefix_096
public import Structure.PSTR_BuildLower_LoopEnvironment_086

/-! A positive actual countdown cycle carries full NEW-C capacity and
every fitted high-cache word at the SAME endpoint as source/Data. The
recursive body supplies one actual witness; head/body/tail are not reset or
replaced by a different run. Whole-prefix safety remains separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopEndCycle
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (body : Program) (counter depth : Nat)
    (hc : counter < 21) (executable : SourceRep.EndExecutable q full used body (depth + 1))
    (environment : Nat → Nat) (hpositive : environment counter ≠ 0)
    (hfit : Fits (bits q full) (environment counter)) (logical : State)
    (context : SourceContext.Context q full (body.eval (dimensionROM full.length q (t q full)) environment) logical)
    (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap) (shape : ASTShape.Shape body)
    (values : ExprBounds.allExprNodesFit (bits q full) (dimensionROM full.length q (t q full)) environment body)
    (hdepth : programRepeatDepth body + (depth + 1) ≤ 3)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock (64 + counter) left.length
      (lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock (64 + counter) left.length
      (lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)) ++ right).length)) :
    ∃ count ≤ ASTBudget.budget body (dimensionROM full.length q (t q full)) + 14,
      let code := lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)
      let after := packingRun (CompactControllerClaims.controllerInput q full used)
        (left ++ relativeLoopBlock (64 + counter) left.length code ++ right) count state
      SourceRep.Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (body.eval (dimensionROM full.length q (t q full)) environment) logical) after ∧
      RuntimeData.Data q full after.heap ∧ after.pc = BitVec.ofNat _ (5 * left.length) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter (environment counter - 1) address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + (depth + 1) ∨ 99 ≤ offset) →
        offset ≠ 64 + counter → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let code := lowerProgram ConcreteAST.ports body (left.length + 5) (depth + 1)
  let head := relativeLoopHead (64 + counter) (5 * (left.length + code.length + 14))
  let tail := relativeLoopTail (64 + counter) (5 * left.length)
  let whole := left ++ relativeLoopBlock (64 + counter) left.length code ++ right
  let tested := packingRun runtime whole 5 state
  have headPost := LoopData.head_data q full runtime (64 + counter) left code right logical state hrep data hpc ha hcode hpcfit
  have counterValue : (state.heap (state.register .address + BitVec.ofNat _ (64 + counter))).toNat = environment counter := by
    rw [henv counter hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 5)) := by
    simpa only [counterValue, ite_eq_right hpositive] using headPost.2.2.2.2.2
  have testedEnv : ∀ address < 21,
      tested.heap (tested.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address) := by
    intro address had
    rw [headPost.2.2.1, headPost.2.2.2.1]
    exact henv address had
  have headLength : head.length = 5 := rfl
  have headKeeps := ControlPrefix.head_keeps q full runtime (64 + counter) left code right state bounded hpc ha hcode hpcfit
  obtain ⟨bodyCount, bodyBound, bodyPost⟩ := executable hq hl environment logical context tested
    headPost.1 headPost.2.1 (headKeeps 5 le_rfl).1 shape values hdepth testedEnv (left ++ head) (tail ++ right)
    (by simpa only [List.length_append, headLength] using testedPC) headPost.2.2.2.2.1
    (by simpa only [List.length_append, headLength, relativeLoopBlock, List.append_assoc, head, tail, code] using hcode)
    (by simpa only [List.length_append, headLength, relativeLoopBlock, List.append_assoc, head, tail, code] using hpcfit)
  let done := packingRun runtime whole bodyCount tested
  have post : SourceRep.Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (body.eval (dimensionROM full.length q (t q full)) environment) logical) done ∧
      RuntimeData.Data q full done.heap ∧ done.pc = BitVec.ofNat _ (5 * (left.length + 5 + code.length)) ∧ done.halted = false ∧
      (∀ address < 21, done.heap (done.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + (depth + 1) ∨ 99 ≤ offset) →
        done.heap (BitVec.ofNat _ (controlBase q full + offset)) = tested.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full done.heap ∧ ResourceTrace.CacheFrame q full tested.heap done.heap := by
    simpa only [List.length_append, headLength, relativeLoopBlock, List.append_assoc, head, tail, code, done, whole] using bodyPost
  have tailPost := LoopData.tail_data q full hq runtime counter hc left code right _ done
    post.1 post.2.1 post.2.2.1 post.2.2.2.1 hcode hpcfit
  have tailRun := WordLoop.tail_run runtime left code right (64 + counter) hcode hpcfit done post.2.2.1 post.2.2.2.1
  have tailKeeps := ControlPrefix.tail_keeps q full hq runtime (64 + counter) (by omega) left code right done post.1.address
    post.2.2.2.2.2.2.1 post.2.2.1 post.2.2.2.1 hcode hpcfit
  refine ⟨5 + bodyCount + 9, by omega, ?_⟩
  dsimp only
  change SourceRep.Prepared q full _ (packingRun runtime whole (5 + bodyCount + 9) state) ∧ _
  rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add]
  refine ⟨tailPost.1, tailPost.2.1, tailPost.2.2.1, tailPost.2.2.2.1, ?_, ?_, (tailKeeps 9 le_rfl).1, ?_⟩
  · rw [tailRun]
    exact LoopEnvironment.tail_environment q full hq runtime counter hc (5 * left.length) environment done post.2.2.2.2.1 hfit
  · intro offset ho hout hsave hne
    rw [tailPost.2.2.2.2.2]
    have offsetNe : BitVec.ofNat (bits q full) (controlBase q full + offset) ≠
        done.register .address + BitVec.ofNat _ (64 + counter) := by
      rw [post.1.address, BitVec.ofNat_add_ofNat]
      exact word_address_ne (bank_offset_fits q full hq offset (by omega))
        (bank_offset_fits q full hq (64 + counter) (by omega)) (by omega)
    rw [Function.update_of_ne offsetNe, post.2.2.2.2.2.1 offset ho hout hsave, headPost.2.2.1]
  · intro point hp hf
    exact ((tailKeeps 9 le_rfl).2 point hp hf).trans
      ((post.2.2.2.2.2.2.2 point hp hf).trans (congrFun headPost.2.2.1 _))

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopEndCycle
