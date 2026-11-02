module

public import Paid.PDLower_CalibrationCompute_SumPhaseStrong_063
public import Paid.PDLower_CalibrationCompute_WeightPhase_047
public import Paid.PDLower_CalibrationCompute_EmitMemory_074
public import Paid.PDLower_CalibrationCompute_ResultPrefix_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- Actual outer-cache extension with the complete original workspace
frame. This consumes a physical row, never a supplied q/weight/run. -/
theorem postRow_framed (origin : ℕ) (input : List Cell) (P : Parameters) (base m : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .sumStart) (represented : header.At before base)
    (rowAt : RowAt before header.readBase (P.walkRow (m+1) true P.certificate.Q))
    (fresh : before.register .fresh=.natural base) (level : header.level=m+1)
    (bounded : m<P.certificate.M+1) (outsideRow : base+16≤header.readBase)
    (endpoints : HeapList before header.endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separateEndpoints : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      header.endpoints+index∉workspace base P.certificate.M)
    (cache : HeapList before (resultBase base P.certificate.M) (calibrationPrefix P m))
    (cursor : header.outputCursor=resultBase base P.certificate.M+(calibrationPrefix P m).length) :
    ∃ after : State,Segment origin input before after (2000*(m+2)) ∧
      after.pc=labelAddress origin .levelGate ∧
      ({header with level:=m+2,cursor:=m+1,q:=P.cachedCappedError m, outputCursor:=header.outputCursor+2}).At after base ∧
      HeapList after (resultBase base P.certificate.M) (calibrationPrefix P (m+1)) ∧
      after.register .fresh=.natural base ∧
      after.output=before.output++encodeCalibration
        ((P.calibrationWeightCache P.endpointCache)[m]'(by simpa using bounded)) ∧
      Frame before after base P.certificate.M := by
  have rowSize : header.level<(P.walkRow (m+1) true P.certificate.Q).size := by
    rw [PDROC.endpointWalkRow_size,level]
    omega
  obtain ⟨summed,sumRun,sumPC,sumHeader,sumFresh,sumOutput,sumMemory⟩ :=
    sumPhase_framed origin input base (P.walkRow (m+1) true P.certificate.Q)
      before header position represented rowAt fresh outsideRow rowSize
  let summedHeader : Header := {header with cursor:=m+1,q:=P.cachedCappedError m}
  have summedRepresented : summedHeader.At summed base := by
    simpa only [summedHeader,level,←originalCalibration_error P m] using sumHeader
  have sumFrame : Frame before summed base P.certificate.M := sumFrame_workspace sumMemory
  have endpointCache : HeapList summed summedHeader.endpoints (encodeList encodeEndpoint P.endpointCache.toList) :=
    endpoints.memoryFrame _ sumFrame separateEndpoints
  have outsideCache : base+16≤resultBase base P.certificate.M := by unfold resultBase; omega
  have resultCache : HeapList summed (resultBase base P.certificate.M) (calibrationPrefix P m) :=
    cache.memoryFrame (sumRegion base) sumMemory (by
      intro index inside
      simp only [sumRegion,Finset.mem_insert,Finset.mem_singleton]
      omega)
  obtain ⟨weighted,weightRun,weightPC,weightHeader,weightFresh,weightValue,weightHeap,weightLive,weightOutput⟩ :=
    weightPhase origin input P base summed summedHeader sumPC summedRepresented sumFresh endpointCache
      (by dsimp [summedHeader]; omega) (by dsimp [summedHeader]; omega)
  have weightedCache : HeapList weighted (resultBase base P.certificate.M) (calibrationPrefix P m) := by
    simpa only [HeapList,heapSegment,weightHeap,weightLive] using resultCache
  let weight := computedWeight (P.endpointConstant m).error (P.cachedCappedError m)
  have value : weighted.register .value=.rational weight := by
    simpa only [summedHeader,level,Nat.add_sub_cancel,weight] using weightValue
  let completed := emitResult weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight
  let after : State := {completed with pc:=labelAddress origin .levelGate}
  have body : linearExecute input (basicBlock .emit).body weighted=some completed := by
    simpa only [summedHeader,level,completed] using
      emit_execute input weighted base summedHeader weight weightHeader weightFresh value (by dsimp [summedHeader]; omega)
  have emitRun : Segment origin input weighted after 390 :=
    segment_go origin .emit .levelGate input weighted completed weightPC body rfl
  have headerAfter : ({header with
      level:=m+2,cursor:=m+1,q:=P.cachedCappedError m,
      outputCursor:=header.outputCursor+2}).At after base := by
    simpa only [summedHeader,level,Nat.add_assoc,after,completed,Header.At,HeapList,heapSegment] using
      emit_header weight weightHeader (by dsimp [summedHeader]; omega)
  have cacheAfter : HeapList after (resultBase base P.certificate.M) (calibrationPrefix P (m+1)) := by
    rw [calibrationPrefix_succ P m bounded,originalCalibration_pair P m bounded]
    change HeapList (emitResult weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight) _ _
    rw [cursor]
    exact emit_cache weightedCache (m+1) (P.cachedCappedError m) weight outsideCache
  have length := calibrationPrefix_length P m (by omega)
  have current : header.outputCursor∈workspace base P.certificate.M := by
    have equal : header.outputCursor=base+(16+2*rowWidth P.certificate.M+1+2*m) := by
      rw [cursor,length]
      unfold resultBase
      omega
    rw [equal]
    exact workspace_member base P.certificate.M _ (by unfold workspaceSize rowWidth; omega)
  have following : header.outputCursor+1∈workspace base P.certificate.M := by
    have equal : header.outputCursor+1=base+(16+2*rowWidth P.certificate.M+2+2*m) := by
      rw [cursor,length]
      unfold resultBase
      omega
    rw [equal]
    exact workspace_member base P.certificate.M _ (by unfold workspaceSize rowWidth; omega)
  have weightedFrame : Frame summed weighted base P.certificate.M :=
    ⟨fun address _outside => congrFun weightHeap address,fun address _outside => by rw [weightLive]⟩
  have emitFrame : Frame weighted after base P.certificate.M :=
    emit_frame weighted base P.certificate.M header.outputCursor (m+1) (P.cachedCappedError m) weight current following
  refine ⟨after,((sumRun.trans weightRun).trans emitRun).mono (by rw [level]; omega),rfl,
    headerAfter,cacheAfter,?_,?_,(sumFrame.trans weightedFrame).trans emitFrame⟩
  · exact (emit_fresh weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight).trans weightFresh
  · change weighted.output++[.rational (P.cachedCappedError m),.rational weight]=_
    rw [weightOutput,sumOutput,originalCalibration_pair P m bounded]

end PDLower.CalibrationCompute
