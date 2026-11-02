module

public import Paid.PDROC_BitVM_VM_Phases_Initial_004
public import Paid.PDROC_BitVM_VM_Phases_Simulation_005
public import Paid.PDROC_BitVM_VM_Phases_Join_006
public import Paid.PDROC_BitVM_VM_Phases_Calls_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.Phases

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Common.IO

/-- The actual eight-phase FUNCTIONAL path. Source Runs and their output
equalities are internal producer interfaces; the final assembly supplies
them from the fixed real preparation and core programs. Nothing here is
installed as a logical RAM state, event list, input-dependent code or fuel
in the finite machine store. No uniform cost substitution is claimed.

Each next call consumes the preceding actual returned var/stk. In
particular prepare's physical output is finalized, genuinely remounted,
and reset before the core starts. The final artifact on0 is not cleared. -/
theorem execute_eight_phases (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    ∀ (raw prepared artifactCells : List Cell)
      (prepareStates : List PaperProofs.Paid.Computation.State)
      (prepareFinal : PaperProofs.Paid.Computation.State)
      (coreStates : List PaperProofs.Paid.Computation.State)
      (coreFinal : PaperProofs.Paid.Computation.State),
      raw.length = 6 → Runs prepareCode raw prepareStates prepareFinal →
      prepareFinal.output = prepared → prepared.length = 13 →
      Runs coreCode prepared coreStates coreFinal → coreFinal.output = artifactCells →
      ∃ (terminal : State backend prepareCode coreCode)
        (_path : ActualPath (TM2.step (program backend prepareCode coreCode))
          (before backend prepareCode coreCode (rawContents (encodeBits raw))) terminal),
        TM2.step (program backend prepareCode coreCode) terminal = none ∧
          terminal.stk 0 = encodeBits artifactCells := by
  -- These two fixed C,d choices precede ALL source inputs and traces.
  obtain ⟨prepareC, prepareD, _prepareCPositive, _prepareDPositive, prepareCall⟩ :=
    Calls.source_caller backend prepareCode coreCode false
  obtain ⟨coreC, coreD, _coreCPositive, _coreDPositive, coreCall⟩ :=
    Calls.source_caller backend prepareCode coreCode true
  intro raw prepared artifactCells prepareStates prepareFinal coreStates coreFinal
    rawSize prepareRuns prepareOutput preparedSize coreRuns coreOutput
  let physical := rawContents (encodeBits raw)
  let firstStore := initial backend prepareCode coreCode
  obtain ⟨rawMounted, rawMountedLabel, rawMountedData, rawMountPath, _rawMountTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .mountRaw firstStore physical _ _
      (Calls.mount_call backend prepareCode coreCode false firstStore raw physical rawSize
        (rawContents_zero (encodeBits raw)))
  have rawBoot : entryState backend prepareCode coreCode .mountRaw firstStore physical =
      before backend prepareCode coreCode physical := initial_cfg backend prepareCode coreCode physical
  have bootMountPath : ActualPath (TM2.step (program backend prepareCode coreCode))
      (before backend prepareCode coreCode physical) rawMounted := by
    rw [← rawBoot]
    exact rawMountPath
  obtain ⟨rawMountReturn, _rawMountReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .mountRaw .resetPrepare rfl rawMounted rawMountedLabel
  obtain ⟨prepareReset, prepareResetLabel, prepareResetData, prepareResetPath, _prepareResetTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .resetPrepare rawMounted.var rawMounted.stk _ _
      (Calls.reset_call backend prepareCode coreCode false rawMounted.var raw rawMounted.stk rawMountedData.banks)
  obtain ⟨prepareResetReturn, _prepareResetReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .resetPrepare .prepare rfl prepareReset prepareResetLabel
  obtain ⟨preparedSource, preparedSourceLabel, preparedSourceData, prepareSourcePath, _prepareSourceTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .prepare prepareReset.var prepareReset.stk _ _
      (prepareCall raw prepareStates prepareFinal prepareReset.stk prepareReset.var rawSize
        prepareRuns prepareResetData.1)
  obtain ⟨prepareSourceReturn, _prepareSourceReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .prepare .finalizePrepare rfl preparedSource preparedSourceLabel
  obtain ⟨preparedFinalized, preparedFinalizedLabel, preparedFinalizedData, prepareFinalizePath, _prepareFinalizeTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .finalizePrepare preparedSource.var preparedSource.stk _ _
      (Calls.finalize_observables backend prepareCode coreCode false preparedSource.var raw prepareFinal
        (BoundaryBudget.actualHistory prepareCode prepareStates) preparedSource.stk preparedSourceData.toObservables)
  have preparedWord : preparedFinalized.stk 0 = encodeBits prepared := by
    simpa only [prepareOutput] using preparedFinalizedData.1
  obtain ⟨prepareFinalizeReturn, _prepareFinalizeReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .finalizePrepare .mountPrepared rfl
      preparedFinalized preparedFinalizedLabel
  obtain ⟨coreMounted, coreMountedLabel, coreMountedData, coreMountPath, _coreMountTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .mountPrepared preparedFinalized.var preparedFinalized.stk _ _
      (Calls.mount_call backend prepareCode coreCode true preparedFinalized.var prepared preparedFinalized.stk
        preparedSize preparedWord)
  obtain ⟨coreMountReturn, _coreMountReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .mountPrepared .resetCore rfl coreMounted coreMountedLabel
  obtain ⟨coreReset, coreResetLabel, coreResetData, coreResetPath, _coreResetTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .resetCore coreMounted.var coreMounted.stk _ _
      (Calls.reset_call backend prepareCode coreCode true coreMounted.var prepared coreMounted.stk coreMountedData.banks)
  obtain ⟨coreResetReturn, _coreResetReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .resetCore .core rfl coreReset coreResetLabel
  obtain ⟨coreSource, coreSourceLabel, coreSourceData, coreSourcePath, _coreSourceTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .core coreReset.var coreReset.stk _ _
      (coreCall prepared coreStates coreFinal coreReset.stk coreReset.var preparedSize coreRuns coreResetData.1)
  obtain ⟨coreSourceReturn, _coreSourceReturnTime⟩ :=
    Calls.advance_path backend prepareCode coreCode .core .finalizeCore rfl coreSource coreSourceLabel
  obtain ⟨coreFinalized, coreFinalizedLabel, coreFinalizedData, coreFinalizePath, _coreFinalizeTime⟩ :=
    Calls.caller_path backend prepareCode coreCode .finalizeCore coreSource.var coreSource.stk _ _
      (Calls.finalize_observables backend prepareCode coreCode true coreSource.var prepared coreFinal
        (BoundaryBudget.actualHistory coreCode coreStates) coreSource.stk coreSourceData.toObservables)
  obtain ⟨terminal, halted, finalData, finalPath, _finalTime⟩ :=
    Calls.finish_path backend prepareCode coreCode coreFinalized coreFinalizedLabel
  have artifactWord : terminal.stk 0 = encodeBits artifactCells := by
    rw [finalData]
    simpa only [coreOutput] using coreFinalizedData.1
  let path1 := bootMountPath.trans rawMountReturn
  let path2 := path1.trans prepareResetPath
  let path3 := path2.trans prepareResetReturn
  let path4 := path3.trans prepareSourcePath
  let path5 := path4.trans prepareSourceReturn
  let path6 := path5.trans prepareFinalizePath
  let path7 := path6.trans prepareFinalizeReturn
  let path8 := path7.trans coreMountPath
  let path9 := path8.trans coreMountReturn
  let path10 := path9.trans coreResetPath
  let path11 := path10.trans coreResetReturn
  let path12 := path11.trans coreSourcePath
  let path13 := path12.trans coreSourceReturn
  let path14 := path13.trans coreFinalizePath
  let path := path14.trans finalPath
  exact ⟨terminal, path, halted, artifactWord⟩

end PDROC.BitVM.VM.Phases
