module

public import Paid.PDLower_CalibrationCompute_OuterGate_071
public import Paid.PDLower_CalibrationCompute_RowCall_076
public import Paid.PDLower_CalibrationCompute_PostRowFramed_077

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem outerStep_cost_bound (Q count : ℕ) :
    165+10000*(Q+1)*(count+2)+2000*(count+2)≤13000*(Q+1)*(count+2) := by
  have scale : count+2≤(Q+1)*(count+2) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (count+2) (by omega : 1≤Q+1)
  have extra := Nat.mul_le_mul_left 2000 scale
  have reserve : 165≤1000*((Q+1)*(count+2)) := by omega
  calc
    _ = 10000*((Q+1)*(count+2))+(165+2000*(count+2)) := by ring
    _ ≤ 10000*((Q+1)*(count+2))+(1000*((Q+1)*(count+2))+2000*((Q+1)*(count+2))) :=
      Nat.add_le_add_left (Nat.add_le_add reserve extra) _
    _ = _ := by ring

/-- Invariant produced by the actual head and maintained by the outer
loop. The varying row words remain the actual physical header fields. -/
structure OuterReady (P : Parameters) (base endpoints returnPC count : ℕ) (header : Header) (state : State) : Prop where
  represented : header.At state base
  M : header.M=P.certificate.M
  Q : header.Q=P.certificate.Q
  gamma : header.gamma=P.certificate.gamma
  endpointAddress : header.endpoints=endpoints
  returnAddress : header.returnPC=returnPC
  level : header.level=count+1
  cursor : header.outputCursor=resultBase base P.certificate.M+(calibrationPrefix P count).length
  fresh : state.register .fresh=.natural base
  endpointHeap : HeapList state endpoints (encodeList encodeEndpoint P.endpointCache.toList)
  cache : HeapList state (resultBase base P.certificate.M) (calibrationPrefix P count)

/-- One genuine outer iteration, including the actual gate, complete
original Q-row, summation, endpoint weight calculation and two emissions. -/
theorem outerStep (P : Parameters) (origin base endpoints returnPC count : ℕ) (input : List Cell)
    (before : State) (header : Header) (ready : OuterReady P base endpoints returnPC count header before)
    (position : before.pc=labelAddress origin .levelGate) (bounded : count<P.certificate.M+1)
    (separate : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+index∉workspace base P.certificate.M) :
    ∃ (after : State) (afterHeader : Header),Segment origin input before after (13000*(P.certificate.Q+1)*(count+2)) ∧
      after.pc=labelAddress origin .levelGate ∧ OuterReady P base endpoints returnPC (count+1) afterHeader after ∧
      after.output=before.output++encodeCalibration
        ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using bounded)) ∧
      Frame before after base P.certificate.M := by
  obtain ⟨entered,gateRun,gatePC,gateHeader,gateFresh,gateHeap,gateLive,gateOutput⟩ :=
    levelGate_continue origin input base before header position ready.represented ready.fresh
      (by rw [ready.M,ready.level]; omega)
  have gateEndpoint : HeapList entered endpoints (encodeList encodeEndpoint P.endpointCache.toList) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.endpointHeap
  have gateCache : HeapList entered (resultBase base P.certificate.M) (calibrationPrefix P count) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.cache
  obtain ⟨rowState,rowRun,rowPC,rowHeader,rowAt,rowFresh,rowOutput,rowMemory⟩ :=
    rowCall P origin base input entered header gateHeader gateFresh ready.M ready.Q ready.gamma gatePC
      (by rw [ready.level]; omega)
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
  have outsideRow : base+16≤rowHeaderValue.readBase := by
    change base+16≤(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
    have buffers := PDROC.CalibrationRow.rowPointers_buffers base P.certificate.M P.certificate.Q
    rcases buffers with ⟨read,_write⟩|⟨read,_write⟩
    · rw [read]
      exact Nat.le_refl _
    · rw [read]
      exact Nat.le_add_right (base+16) (rowWidth P.certificate.M)
  obtain ⟨after,postRun,pc,postHeader,cache,fresh,output,postFrame⟩ :=
    postRow_framed origin input P base count rowState rowHeaderValue rowPC rowHeader actualRow rowFresh
      ready.level bounded outsideRow rowEndpoint
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
