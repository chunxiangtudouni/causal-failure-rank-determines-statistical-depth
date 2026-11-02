module

public import Paid.PDLower_CalibrationCompute_OuterStep_078
public import Paid.PDLower_CalibrationCompute_PostRowBits_114
public import Paid.PDLower_CalibrationCompute_GateCallerBits_116
public import Paid.PDLower_CalibrationCompute_RowCallBits_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- One genuine outer iteration, including the actual gate, complete
original Q-row, summation, endpoint weight calculation and two emissions. -/
theorem outerStep_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma count : ℕ) (input : List Cell)
    (initialCaller before : State) (header : Header) (ready : OuterReady P base endpoints returnPC count header before)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (position : before.pc=labelAddress origin .levelGate) (bounded : count<P.certificate.M+1)
    (separate : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+index∉workspace base P.certificate.M) :
    ∃ (after : State) (afterHeader : Header),BitSegment origin input before after (13000*(P.certificate.Q+1)*(count+2)) (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=labelAddress origin .levelGate ∧ OuterReady P base endpoints returnPC (count+1) afterHeader after ∧
      after.output=before.output++encodeCalibration
        ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using bounded)) ∧
      Frame before after base P.certificate.M := by
  obtain ⟨entered,gateRun,gatePC,gateHeader,gateFresh,gateHeap,gateLive,gateOutput⟩ :=
    levelGate_continue_bits P origin base endpoints returnPC callerBudget Lgamma input initialCaller before header
      arguments initialSafe position ready.represented ready.fresh safe ready.M
      (by rw [ready.M,ready.level]; omega)
  have gateEndpoint : HeapList entered endpoints (encodeList encodeEndpoint P.endpointCache.toList) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.endpointHeap
  have gateCache : HeapList entered (resultBase base P.certificate.M) (calibrationPrefix P count) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.cache
  obtain ⟨rowState,rowRun,rowPC,rowHeader,rowAt,rowFresh,rowOutput,rowMemory⟩ :=
    rowCall_bits P origin base Lgamma (calleeOperandBudget P origin callerBudget Lgamma) input entered header
      gateHeader gateFresh ready.M ready.Q ready.gamma gatePC (by rw [ready.level];omega) gateRun.final
      (calleeOperandBudget_row P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe gammaBits)
  let rowHeaderValue : Header := {header with
    clock:=P.certificate.Q,cursor:=2*header.level+1,width:=2*header.level+1,
    readBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1,
    writeBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2}
  have rowEndpoint : HeapList rowState rowHeaderValue.endpoints (encodeList encodeEndpoint P.endpointCache.toList) := by
    have preserved := gateEndpoint.memoryFrame _ (rowFrame_workspace rowMemory) separate
    simpa only [rowHeaderValue,ready.endpointAddress] using preserved
  have rowCache : HeapList rowState (resultBase base P.certificate.M) (calibrationPrefix P count) :=
    gateCache.memoryFrame _ rowMemory (by
      intro index inside
      exact PDROC.CalibrationRow.result_outside base P.certificate.M _ (Nat.le_add_right _ _))
  have actualRow : RowAt rowState rowHeaderValue.readBase (P.walkRow (count+1) true P.certificate.Q) := by
    simpa only [rowHeaderValue,ready.level] using rowAt
  obtain ⟨after,postRun,pc,postHeader,cache,fresh,output,postFrame⟩ :=
    postRow_bits P origin base endpoints returnPC callerBudget Lgamma count input initialCaller rowState rowHeaderValue
      arguments initialSafe gammaBits rowPC rowHeader actualRow rowFresh rowRun.final
      (PDROC.CalibrationRow.rowPointers_buffers base P.certificate.M P.certificate.Q)
      ready.level bounded ready.endpointAddress rowEndpoint
      (by simpa only [rowHeaderValue,ready.endpointAddress] using separate)
      rowCache ready.cursor
  let afterHeader : Header := {rowHeaderValue with
    level:=count+2,cursor:=count+1,q:=P.cachedCappedError count,outputCursor:=rowHeaderValue.outputCursor+2}
  have length := calibrationPrefix_length P count (by omega)
  have nextLength := calibrationPrefix_length P (count+1) (by omega)
  have gateFrame : Frame before entered base P.certificate.M :=
    ⟨fun address _outside => congrFun gateHeap address,fun address _outside => by rw [gateLive]⟩
  have frame : Frame before after base P.certificate.M :=
    (gateFrame.trans (rowFrame_workspace rowMemory)).trans postFrame
  have endpointHeap : HeapList after endpoints (encodeList encodeEndpoint P.endpointCache.toList) :=
    ready.endpointHeap.memoryFrame _ frame separate
  have next : OuterReady P base endpoints returnPC (count+1) afterHeader after := by
    refine ⟨postHeader,ready.M,ready.Q,ready.gamma,ready.endpointAddress,
      ready.returnAddress,?_,?_,fresh,endpointHeap,cache⟩
    · rfl
    · dsimp [afterHeader,rowHeaderValue]
      rw [ready.cursor,length,nextLength]
      omega
  refine ⟨after,afterHeader,((gateRun.trans rowRun).trans postRun).mono ?_,pc,next,?_,frame⟩
  · simpa only [ready.level,Nat.add_assoc] using outerStep_cost_bound P.certificate.Q count
  · rw [output,rowOutput,gateOutput]

end PDLower.CalibrationCompute
