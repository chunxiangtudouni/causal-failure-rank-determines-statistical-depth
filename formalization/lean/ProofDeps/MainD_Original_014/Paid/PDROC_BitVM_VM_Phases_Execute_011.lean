module

public import Paid.PDROC_BitVM_VM_Phases_Execute_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Execute

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-- One selected eight-stage actual path, with its finite schedule.
The two source constants precede ALL inputs. P/Q are internal upper
bounds on those real source calls; the parent substitutes the proved
original resource bounds and eliminates them from the paper theorem.
All six other costs and all eight returned data sizes are established
on this very path by real caller occupancy, with no free tape change. -/
theorem execute_bounded (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    ∃ prepareC prepareD coreC coreD : ℕ,
      0 < prepareC ∧ 0 < prepareD ∧ 0 < coreC ∧ 0 < coreD ∧
      ∀ (raw prepared artifactCells : List Cell)
        (prepareStates : List PaperProofs.Paid.Computation.State)
        (prepareFinal : PaperProofs.Paid.Computation.State)
        (coreStates : List PaperProofs.Paid.Computation.State)
        (coreFinal : PaperProofs.Paid.Computation.State) (P Q : ℕ),
        raw.length = 6 → Runs prepareCode raw prepareStates prepareFinal →
        prepareFinal.output = prepared → prepared.length = 13 →
        Runs coreCode prepared coreStates coreFinal → coreFinal.output = artifactCells →
        CFG.Complete.totalBudget prepareC prepareD prepareCode raw prepareStates + 1 ≤ P →
        CFG.Complete.totalBudget coreC coreD coreCode prepared coreStates + 1 ≤ Q →
        ∃ (terminal : State backend prepareCode coreCode)
          (path : ActualPath (TM2.step (program backend prepareCode coreCode))
            (before backend prepareCode coreCode (rawContents (encodeBits raw))) terminal),
          TM2.step (program backend prepareCode coreCode) terminal = none ∧
          terminal.stk 0 = encodeBits artifactCells ∧
          path.posts.length + 1 ≤ Polynomial.schedule8 Resources.coefficient
            (Calls.globalPushCap backend prepareCode coreCode) (encodeBits raw).length P Q := by
  obtain ⟨prepareC, prepareD, prepareCPositive, prepareDPositive, prepareCall⟩ :=
    Calls.source_caller backend prepareCode coreCode false
  obtain ⟨coreC, coreD, coreCPositive, coreDPositive, coreCall⟩ :=
    Calls.source_caller backend prepareCode coreCode true
  refine ⟨prepareC, prepareD, coreC, coreD, prepareCPositive, prepareDPositive,
    coreCPositive, coreDPositive, ?_⟩
  intro raw prepared artifactCells prepareStates prepareFinal coreStates coreFinal P Q
    rawSize prepareRuns prepareOutput preparedSize coreRuns coreOutput prepareBound coreBound
  rw [← initial_cfg backend prepareCode coreCode (rawContents (encodeBits raw))]
  let physical := rawContents (encodeBits raw)
  let firstStore := initial backend prepareCode coreCode
  let I := (encodeBits raw).length
  let path0 := ActualPath.refl (step := TM2.step (program backend prepareCode coreCode))
    (entryState backend prepareCode coreCode .mountRaw firstStore physical)
  have time0 : path0.posts.length ≤ Polynomial.prefixBudget Resources.coefficient
      (Calls.globalPushCap backend prepareCode coreCode) I P Q 0 := Nat.zero_le _
  have physicalSize : Kernel.NatInstruction.dataSize physical ≤ phaseData backend prepareCode coreCode I P Q 0 :=
    (raw_data_size (encodeBits raw)).le
  obtain ⟨rawMounted, rawMountedLabel, rawMountedData, rawMountedSize, rawMountPath, rawMountTime⟩ :=
    control_call backend prepareCode coreCode .mountRaw firstStore physical _ _ I P Q 0
      (by decide) (by decide) physicalSize
      (Calls.mount_call backend prepareCode coreCode false firstStore raw physical rawSize (rawContents_zero _))
      (Resources.mount_uniform raw [] physical (by simpa only [List.append_nil] using rawContents_zero (encodeBits raw)))
  obtain ⟨rawMountReturn, rawMountReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .mountRaw .resetPrepare rfl rawMounted rawMountedLabel
  let path1 := (path0.trans rawMountPath).trans rawMountReturn
  have time1 := append_scheduled backend prepareCode coreCode I P Q 0
    path0 rawMountPath rawMountReturn time0 rawMountTime rawMountReturnTime
  obtain ⟨prepareReset, prepareResetLabel, prepareResetData, prepareResetSize, prepareResetPath, prepareResetTime⟩ :=
    control_call backend prepareCode coreCode .resetPrepare rawMounted.var rawMounted.stk _ _ I P Q 1
      (by decide) (by decide) rawMountedSize
      (Calls.reset_call backend prepareCode coreCode false rawMounted.var raw rawMounted.stk rawMountedData.banks)
      (Resources.reset_uniform rawMounted.stk)
  obtain ⟨prepareResetReturn, prepareResetReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .resetPrepare .prepare rfl prepareReset prepareResetLabel
  let path2 := (path1.trans prepareResetPath).trans prepareResetReturn
  have time2 := append_scheduled backend prepareCode coreCode I P Q 1
    path1 prepareResetPath prepareResetReturn time1 prepareResetTime prepareResetReturnTime
  have prepareActual := prepareCall raw prepareStates prepareFinal prepareReset.stk prepareReset.var
    rawSize prepareRuns prepareResetData.1
  have prepareLarger : CFG.Complete.totalBudget prepareC prepareD prepareCode raw prepareStates + 1 ≤
      phaseBudget backend prepareCode coreCode I P Q 2 := prepareBound
  obtain ⟨preparedSource, preparedSourceLabel, preparedSourceData, _preparedSourceSize, prepareSourcePath, prepareSourceTime⟩ :=
    scheduled_call backend prepareCode coreCode .prepare prepareReset.var prepareReset.stk _ I P Q 2 prepareResetSize
      (Calls.CallerRun.mono backend prepareCode coreCode .prepare prepareReset.var prepareReset.stk _ _ _
        prepareActual prepareLarger)
  obtain ⟨prepareSourceReturn, prepareSourceReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .prepare .finalizePrepare rfl preparedSource preparedSourceLabel
  let path3 := (path2.trans prepareSourcePath).trans prepareSourceReturn
  have time3 := append_scheduled backend prepareCode coreCode I P Q 2
    path2 prepareSourcePath prepareSourceReturn time2 prepareSourceTime prepareSourceReturnTime
  obtain ⟨preparedFinalized, preparedFinalizedLabel, preparedFinalizedData, preparedFinalizedSize,
      prepareFinalizePath, prepareFinalizeTime⟩ :=
    control_call backend prepareCode coreCode .finalizePrepare preparedSource.var preparedSource.stk _ _ I P Q 3
      (by decide) (by decide) _preparedSourceSize
      (Calls.finalize_observables backend prepareCode coreCode false preparedSource.var raw prepareFinal
        (BoundaryBudget.actualHistory prepareCode prepareStates) preparedSource.stk preparedSourceData.toObservables)
      (Resources.finalize_uniform preparedSource.stk)
  have preparedWord : preparedFinalized.stk 0 = encodeBits prepared := by
    simpa only [prepareOutput] using preparedFinalizedData.1
  obtain ⟨prepareFinalizeReturn, prepareFinalizeReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .finalizePrepare .mountPrepared rfl
      preparedFinalized preparedFinalizedLabel
  let path4 := (path3.trans prepareFinalizePath).trans prepareFinalizeReturn
  have time4 := append_scheduled backend prepareCode coreCode I P Q 3
    path3 prepareFinalizePath prepareFinalizeReturn time3 prepareFinalizeTime prepareFinalizeReturnTime
  obtain ⟨coreMounted, coreMountedLabel, coreMountedData, coreMountedSize, coreMountPath, coreMountTime⟩ :=
    control_call backend prepareCode coreCode .mountPrepared preparedFinalized.var preparedFinalized.stk _ _ I P Q 4
      (by decide) (by decide) preparedFinalizedSize
      (Calls.mount_call backend prepareCode coreCode true preparedFinalized.var prepared preparedFinalized.stk
        preparedSize preparedWord)
      (Resources.mount_uniform prepared [] preparedFinalized.stk (by simpa only [List.append_nil] using preparedWord))
  obtain ⟨coreMountReturn, coreMountReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .mountPrepared .resetCore rfl coreMounted coreMountedLabel
  let path5 := (path4.trans coreMountPath).trans coreMountReturn
  have time5 := append_scheduled backend prepareCode coreCode I P Q 4
    path4 coreMountPath coreMountReturn time4 coreMountTime coreMountReturnTime
  obtain ⟨coreReset, coreResetLabel, coreResetData, coreResetSize, coreResetPath, coreResetTime⟩ :=
    control_call backend prepareCode coreCode .resetCore coreMounted.var coreMounted.stk _ _ I P Q 5
      (by decide) (by decide) coreMountedSize
      (Calls.reset_call backend prepareCode coreCode true coreMounted.var prepared coreMounted.stk coreMountedData.banks)
      (Resources.reset_uniform coreMounted.stk)
  obtain ⟨coreResetReturn, coreResetReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .resetCore .core rfl coreReset coreResetLabel
  let path6 := (path5.trans coreResetPath).trans coreResetReturn
  have time6 := append_scheduled backend prepareCode coreCode I P Q 5
    path5 coreResetPath coreResetReturn time5 coreResetTime coreResetReturnTime
  have coreActual := coreCall prepared coreStates coreFinal coreReset.stk coreReset.var preparedSize coreRuns coreResetData.1
  have coreLarger : CFG.Complete.totalBudget coreC coreD coreCode prepared coreStates + 1 ≤
      phaseBudget backend prepareCode coreCode I P Q 6 := coreBound
  obtain ⟨coreSource, coreSourceLabel, coreSourceData, coreSourceSize, coreSourcePath, coreSourceTime⟩ :=
    scheduled_call backend prepareCode coreCode .core coreReset.var coreReset.stk _ I P Q 6 coreResetSize
      (Calls.CallerRun.mono backend prepareCode coreCode .core coreReset.var coreReset.stk _ _ _ coreActual coreLarger)
  obtain ⟨coreSourceReturn, coreSourceReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .core .finalizeCore rfl coreSource coreSourceLabel
  let path7 := (path6.trans coreSourcePath).trans coreSourceReturn
  have time7 := append_scheduled backend prepareCode coreCode I P Q 6
    path6 coreSourcePath coreSourceReturn time6 coreSourceTime coreSourceReturnTime
  obtain ⟨coreFinalized, coreFinalizedLabel, coreFinalizedData, _coreFinalizedSize, coreFinalizePath, coreFinalizeTime⟩ :=
    control_call backend prepareCode coreCode .finalizeCore coreSource.var coreSource.stk _ _ I P Q 7
      (by decide) (by decide) coreSourceSize
      (Calls.finalize_observables backend prepareCode coreCode true coreSource.var prepared coreFinal
        (BoundaryBudget.actualHistory coreCode coreStates) coreSource.stk coreSourceData.toObservables)
      (Resources.finalize_uniform coreSource.stk)
  obtain ⟨terminal, halted, finalData, finalPath, finalTime⟩ :=
    Calls.finish_path backend prepareCode coreCode coreFinalized coreFinalizedLabel
  let path8 := (path7.trans coreFinalizePath).trans finalPath
  have time8 := append_scheduled backend prepareCode coreCode I P Q 7
    path7 coreFinalizePath finalPath time7 coreFinalizeTime finalTime
  have artifactWord : terminal.stk 0 = encodeBits artifactCells := by
    rw [finalData]
    simpa only [coreOutput] using coreFinalizedData.1
  exact ⟨terminal, path8, halted, artifactWord, Nat.add_le_add_right time8 1⟩

end PDROC.BitVM.VM.Phases.Execute
