module

public import Structure.PSTR_BuildLower_CountdownEndResources_110
public import Structure.PSTR_BuildLower_LoopFrames_091

/-! Real save/bound, reversed source countdown and restore carry source,
full NEW-C capacity and every high-cache word at ONE actual endpoint. All
resource phases share their selected counts/states. This does not infer
whole-prefix access/Fits from endpoint facts or add a raw caller premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem repeat_end_executable (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (counter : Nat) (bound : Expr) (body : Program) (depth : Nat)
    (bodyEndExecutable : EndExecutable q full used body (depth + 1)) :
    EndExecutable q full used (.repeat counter bound body) depth := by
  intro hq hl environment logical context state hrep data bounded shape values hdepth henv left right hpc ha hcode hpcfit
  let rom := dimensionROM full.length q (t q full)
  let runtime := CompactControllerClaims.controllerInput q full used
  let setup := relativeRepeatPrefix (64 + counter) (96 + depth) bound
  let loopLeft := left ++ setup
  let bodyCode := lowerProgram ConcreteAST.ports body (loopLeft.length + 5) (depth + 1)
  let loop := relativeLoopBlock (64 + counter) loopLeft.length bodyCode
  let restore := relativeCopy (96 + depth) (64 + counter)
  let whole := left ++ setup ++ loop ++ restore ++ right
  have compiled : lowerProgram ConcreteAST.ports (.repeat counter bound body) left.length depth = setup ++ loop ++ restore := by
    simp only [lowerProgram, setup, loop, loopLeft, bodyCode, restore, List.length_append]
  have codeFit : WordsFit (bits q full) (packingCode whole) := by
    simpa only [compiled, whole, List.append_assoc] using hcode
  have pcFit : Fits (bits q full) (5 * whole.length) := by
    simpa only [compiled, whole, List.append_assoc] using hpcfit
  have hc : counter < 21 := shape.1
  have hsize : bound.size ≤ 29 := shape.2.1
  have hd : depth < 3 := by change (programRepeatDepth body + 1) + depth ≤ 3 at hdepth; omega
  have bodyDepth : programRepeatDepth body + (depth + 1) ≤ 3 := by
    change (programRepeatDepth body + 1) + depth ≤ 3 at hdepth
    omega
  have setupResult := LoopSetup.core_run q full hq runtime counter depth hc hd bound environment
    (by have hh := shape.2.2.1; omega) shape.2.2.2.1 shape.2.1 logical state hrep data henv values.1
    left (loop ++ restore ++ right) hpc ha
    (by simpa only [whole, List.append_assoc, setup] using codeFit)
    (by simpa only [whole, List.append_assoc, setup] using pcFit)
  let middle := packingRun runtime whole setup.length state
  have prelude : setup.length ≤ 212 ∧ Prepared q full logical middle ∧ RuntimeData.Data q full middle.heap ∧
      middle.pc = BitVec.ofNat _ (5 * loopLeft.length) ∧ middle.halted = false ∧
      (∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter (bound.eval rom environment) address)) ∧
      middle.heap (BitVec.ofNat _ (controlBase q full + (96 + depth))) = BitVec.ofNat _ (environment counter) := by
    simpa only [middle, whole, loopLeft, List.length_append, List.append_assoc, setup, rom] using setupResult
  have setupRange : BankRangeFrame (bits := bits q full) runtime setup 64 (128 + bound.size) := by
    have split : setup = relativeCopy (64 + counter) (96 + depth) ++ LexicalSet.code counter bound := by
      simp only [setup, relativeRepeatPrefix, LexicalSet.code, List.append_assoc]
    rw [split]
    apply bankRangeFrame_append
    · exact bankRangeFrame_mono runtime _ (96 + depth) (96 + depth + 1) 64 (128 + bound.size)
        (by omega) (by omega) (ControlDataFrame.copy_range runtime (64 + counter) (96 + depth))
    · exact LexicalSet.code_range runtime counter bound hc
  have setupKeeps := ResourceTrace.bank_actual_keeps q full hq runtime setup 64 (128 + bound.size) (by omega) (by omega)
    setupRange (LoopFrames.setup_straight _ _ _) state hrep.address bounded left (loop ++ restore ++ right) hpc ha
    (by simpa only [whole, List.append_assoc] using codeFit) (by simpa only [whole, List.append_assoc] using pcFit)
  have setupProgramEq : left ++ setup ++ (loop ++ restore ++ right) = whole := by simp only [whole, List.append_assoc]
  rw [setupProgramEq] at setupKeeps
  have middleBounded : GlobalCapacity.Bounded q full middle.heap := (setupKeeps setup.length le_rfl).1
  have preludeCache : ResourceTrace.CacheFrame q full state.heap middle.heap := (setupKeeps setup.length le_rfl).2
  have sourceContext : SourceContext.Context q full (LoopSource.code rom environment counter body (bound.eval rom environment)) logical := context
  obtain ⟨loopCount, loopBound, loopResult⟩ := EndCountdown.run q full used hq hl body counter depth hc bodyEndExecutable
    environment shape.2.2.2.2 bodyDepth loopLeft (restore ++ right)
    (by simpa only [whole, loopLeft, loop, List.append_assoc] using codeFit)
    (by simpa only [whole, loopLeft, loop, List.append_assoc] using pcFit)
    (bound.eval rom environment) (ExprBounds.nodesFit_value values.1) values.2 logical sourceContext
    middle prelude.2.1 prelude.2.2.1 middleBounded prelude.2.2.2.2.2.1 prelude.2.2.2.1 prelude.2.2.2.2.1
  let beforeRestore := packingRun runtime whole loopCount middle
  have loopPost : Prepared q full (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      ((Program.repeat counter bound body).eval rom environment) logical) beforeRestore ∧
      RuntimeData.Data q full beforeRestore.heap ∧
      beforeRestore.pc = BitVec.ofNat _ (5 * (loopLeft.length + bodyCode.length + 14)) ∧ beforeRestore.halted = false ∧
      (∀ address < 21, beforeRestore.heap (beforeRestore.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter 0 address)) ∧
      (∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) → (offset < 96 + (depth + 1) ∨ 99 ≤ offset) →
        offset ≠ 64 + counter → beforeRestore.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          middle.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full beforeRestore.heap ∧ ResourceTrace.CacheFrame q full middle.heap beforeRestore.heap := by
    simpa only [LoopSource.eval_repeat, beforeRestore, whole, loopLeft, loop, bodyCode, List.append_assoc, rom] using loopResult
  have saved : beforeRestore.heap (beforeRestore.register .address + BitVec.ofNat _ (96 + depth)) =
      BitVec.ofNat _ (environment counter) := by
    rw [loopPost.1.address, BitVec.ofNat_add_ofNat,
      loopPost.2.2.2.2.2.1 (96 + depth) (by omega) (by omega) (by omega) (by omega)]
    exact prelude.2.2.2.2.2.2
  have restorePC : beforeRestore.pc = BitVec.ofNat _ (5 * (loopLeft ++ loop).length) := by
    simpa only [List.length_append, loop, relativeLoopBlock_length, Nat.add_assoc] using loopPost.2.2.1
  have restored := copy_data q full hq runtime (96 + depth) (64 + counter) (by omega) (by omega)
    _ beforeRestore loopPost.1 loopPost.2.1 (loopLeft ++ loop) right restorePC loopPost.2.2.2.1
    (by simpa only [whole, loopLeft, restore, List.append_assoc] using codeFit)
    (by simpa only [whole, loopLeft, restore, List.append_assoc] using pcFit)
  have restoreKeeps := ResourceTrace.bank_actual_keeps q full hq runtime restore (64 + counter) (64 + counter + 1)
    (by omega) (by omega) (ControlDataFrame.copy_range runtime (96 + depth) (64 + counter))
    (copy_straight _ _) beforeRestore loopPost.1.address loopPost.2.2.2.2.2.2.1 (loopLeft ++ loop) right
    restorePC loopPost.2.2.2.1
    (by simpa only [whole, loopLeft, List.append_assoc] using codeFit)
    (by simpa only [whole, loopLeft, List.append_assoc] using pcFit)
  have restoreLength : restore.length = 6 := relativeCopy_length _ _
  rw [restoreLength] at restoreKeeps
  have restoreRun := straight_prefix runtime (loopLeft ++ loop) restore right beforeRestore
    (copy_straight _ _) (by simpa only [whole, loopLeft, List.append_assoc] using codeFit)
    (by simpa only [whole, loopLeft, List.append_assoc] using pcFit)
    restorePC loopPost.2.2.2.1 6 (by rw [relativeCopy_length])
  rw [List.take_of_length_le (by rw [relativeCopy_length])] at restoreRun
  have restoredEnv := LoopEnvironment.restore_environment q full hq runtime counter depth hc environment beforeRestore
    (by intro address had hne; simpa only [Function.update_of_ne hne] using loopPost.2.2.2.2.1 address had) saved
  have finalEnv : ∀ address < 21,
      (packingRun runtime ((loopLeft ++ loop) ++ restore ++ right) 6 beforeRestore).heap
        ((packingRun runtime ((loopLeft ++ loop) ++ restore ++ right) 6 beforeRestore).register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (environment address) := by
    rw [restoreRun]
    exact restoredEnv
  have sameRun : packingRun runtime whole (setup.length + loopCount + 6) state =
      packingRun runtime ((loopLeft ++ loop) ++ restore ++ right) 6 beforeRestore := by
    rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add]
  refine ⟨setup.length + loopCount + 6, ?_, ?_⟩
  · have boundZero := ProgramShape.zero_cells_eval bound shape.2.2.1 rom environment (fun _ => 0)
    change setup.length + loopCount + 6 ≤ (fixedExprCode bound).length + 9 +
      bound.eval rom (fun _ => 0) * (ASTBudget.budget body rom + 14) + 11
    have setupLength : setup.length = (fixedExprCode bound).length + 9 := relativeRepeatPrefix_length _ _ _
    change loopCount ≤ bound.eval rom environment * (ASTBudget.budget body rom + 14) + 5 at loopBound
    rw [boundZero] at loopBound
    omega
  · dsimp only
    rw [compiled]
    have physicalProgram : left ++ (setup ++ loop ++ restore) ++ right = whole := by
      simp only [whole, List.append_assoc]
    rw [physicalProgram]
    change Prepared q full _ (packingRun runtime whole (setup.length + loopCount + 6) state) ∧ _
    rw [sameRun]
    refine ⟨restored.1, restored.2.1, ?_, restored.2.2.2.1, ?_, ?_, (restoreKeeps 6 le_rfl).1, ?_⟩
    · calc
        _ = BitVec.ofNat _ (5 * ((loopLeft ++ loop).length + 6)) := restored.2.2.1
        _ = BitVec.ofNat _ (5 * (left.length + (setup ++ loop ++ restore).length)) := by
          congr 1
          simp only [loopLeft, restore, List.length_append, relativeCopy_length]
          omega
    · exact finalEnv
    · intro offset ho hout hsave
      by_cases he : offset = 64 + counter
      · subst offset
        have final := finalEnv counter hc
        have initial := henv counter hc
        rw [restored.1.address, BitVec.ofNat_add_ofNat] at final
        rw [hrep.address, BitVec.ofNat_add_ofNat] at initial
        exact final.trans initial.symm
      · have restoreFrame := LoopFrames.restore_offset q full hq runtime counter depth offset hc ho he beforeRestore
          (loopLeft ++ loop) right restorePC loopPost.2.2.2.1
          (by simpa only [whole, loopLeft, restore, List.append_assoc] using codeFit)
          (by simpa only [whole, loopLeft, restore, List.append_assoc] using pcFit)
        have setupFrame := LoopFrames.setup_offset q full hq runtime counter depth hc hd bound shape.2.1 offset ho he
          (by rcases hsave with h | h <;> omega) state left (loop ++ restore ++ right) hpc ha
          (by simpa only [whole, setup, List.append_assoc] using codeFit)
          (by simpa only [whole, setup, List.append_assoc] using pcFit)
        have loopFrame := loopPost.2.2.2.2.2.1 offset ho hout (by rcases hsave with h | h <;> omega) he
        rw [loopPost.1.address, BitVec.ofNat_add_ofNat] at restoreFrame
        rw [hrep.address, BitVec.ofNat_add_ofNat] at setupFrame
        have setupProgram : left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++
            (loop ++ restore ++ right) = whole := by
          simp only [whole, setup, List.append_assoc]
        rw [setupProgram] at setupFrame
        exact restoreFrame.trans (loopFrame.trans setupFrame)
    · intro point hp hf
      exact ((restoreKeeps 6 le_rfl).2 point hp hf).trans
        ((loopPost.2.2.2.2.2.2.2 point hp hf).trans (preludeCache point hp hf))

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
