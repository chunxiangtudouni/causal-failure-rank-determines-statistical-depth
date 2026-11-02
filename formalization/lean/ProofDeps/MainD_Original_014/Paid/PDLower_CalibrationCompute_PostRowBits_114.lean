module

public import Paid.PDLower_CalibrationCompute_PostRowFramed_077
public import Paid.PDLower_CalibrationCompute_WeightCallerBits_110
public import Paid.PDLower_CalibrationCompute_EmitBits_111
public import Paid.PDLower_CalibrationCompute_SumCallerBits_124

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- The complete actual sum, ratio, stores and two stream appends on
one trace. Every new scalar is bounded from the original initial caller;
the unchanged output and scratch fields retain that same caller budget. -/
theorem postRow_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma m : ℕ)
    (input : List Cell) (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (position : before.pc=labelAddress origin .sumStart) (represented : header.At before base)
    (rowAt : RowAt before header.readBase (P.walkRow (m+1) true P.certificate.Q))
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (buffers : PDROC.CalibrationRow.Buffers base P.certificate.M header.readBase header.writeBase)
    (level : header.level=m+1) (bounded : m<P.certificate.M+1) (endpointAddress : header.endpoints=endpoints)
    (endpointHeap : HeapList before header.endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separateEndpoints : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      header.endpoints+index∉workspace base P.certificate.M)
    (cache : HeapList before (resultBase base P.certificate.M) (calibrationPrefix P m))
    (cursor : header.outputCursor=resultBase base P.certificate.M+(calibrationPrefix P m).length) :
    ∃ after : State,BitSegment origin input before after (2000*(m+2)) (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=labelAddress origin .levelGate ∧
      ({header with level:=m+2,cursor:=m+1,q:=P.cachedCappedError m,outputCursor:=header.outputCursor+2}).At after base ∧
      HeapList after (resultBase base P.certificate.M) (calibrationPrefix P (m+1)) ∧
      after.register .fresh=.natural base ∧
      after.output=before.output++encodeCalibration
        ((P.calibrationWeightCache P.endpointCache)[m]'(by simpa using bounded)) ∧
      Frame before after base P.certificate.M := by
  have actualRow : RowAt before header.readBase (P.walkRow header.level true P.certificate.Q) := by
    simpa only [level] using rowAt
  obtain ⟨summed,sumRun,sumPC,sumHeader,sumFresh,sumOutput,sumMemory⟩ :=
    sumPhase_caller_bits P origin base endpoints returnPC callerBudget Lgamma input initialCaller before header
      arguments initialSafe gammaBits position represented actualRow fresh safe buffers (by omega)
  let summedHeader : Header := {header with cursor:=m+1,q:=P.cachedCappedError m}
  have summedRepresented : summedHeader.At summed base := by
    simpa only [summedHeader,level,←originalCalibration_error P m] using sumHeader
  have sumFrame : Frame before summed base P.certificate.M := sumFrame_workspace sumMemory
  have summedEndpoints : HeapList summed summedHeader.endpoints (encodeList encodeEndpoint P.endpointCache.toList) :=
    endpointHeap.memoryFrame _ sumFrame separateEndpoints
  have outsideCache : base+16≤resultBase base P.certificate.M := by unfold resultBase;omega
  have resultCache : HeapList summed (resultBase base P.certificate.M) (calibrationPrefix P m) :=
    cache.memoryFrame (sumRegion base) sumMemory (by
      intro index inside
      simp only [sumRegion,Finset.mem_insert,Finset.mem_singleton]
      omega)
  obtain ⟨weighted,weightRun,weightPC,weightHeader,weightFresh,weightValue,weightHeap,weightLive,weightOutput⟩ :=
    weightPhase_caller_bits P origin base endpoints returnPC callerBudget Lgamma m input initialCaller summed summedHeader
      arguments initialSafe gammaBits sumPC summedRepresented sumFresh sumRun.final summedEndpoints endpointAddress level bounded rfl
  have weightedCache : HeapList weighted (resultBase base P.certificate.M) (calibrationPrefix P m) := by
    simpa only [HeapList,heapSegment,weightHeap,weightLive] using resultCache
  let weight := computedWeight (P.endpointConstant m).error (P.cachedCappedError m)
  have value : weighted.register .value=.rational weight := weightValue
  let completed := emitResult weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight
  let after : State := {completed with pc:=labelAddress origin .levelGate}
  have length := calibrationPrefix_length P m (by omega)
  have cursorEnd : header.outputCursor+2≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q := by
    rw [cursor,length]
    unfold resultBase rowWidth calleeNaturalCap
    omega
  have emitRun : BitSegment origin input weighted after 390 (calleeOperandBudget P origin callerBudget Lgamma) := by
    simpa only [summedHeader,level,completed,after] using
      emit_caller_bits P origin base endpoints returnPC callerBudget Lgamma input initialCaller weighted summedHeader weight
        arguments initialSafe weightPC weightHeader weightFresh value (by dsimp [summedHeader];omega)
        weightRun.final (by dsimp [summedHeader];omega) cursorEnd
  have headerAfter : ({header with
      level:=m+2,cursor:=m+1,q:=P.cachedCappedError m,
      outputCursor:=header.outputCursor+2}).At after base := by
    simpa only [summedHeader,level,Nat.add_assoc,after,completed,Header.At,HeapList,heapSegment] using
      emit_header weight weightHeader (by dsimp [summedHeader];omega)
  have cacheAfter : HeapList after (resultBase base P.certificate.M) (calibrationPrefix P (m+1)) := by
    rw [calibrationPrefix_succ P m bounded,originalCalibration_pair P m bounded]
    change HeapList (emitResult weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight) _ _
    rw [cursor]
    exact emit_cache weightedCache (m+1) (P.cachedCappedError m) weight outsideCache
  have current : header.outputCursor∈workspace base P.certificate.M := by
    have equal : header.outputCursor=base+(16+2*rowWidth P.certificate.M+1+2*m) := by
      rw [cursor,length]
      unfold resultBase
      omega
    rw [equal]
    exact workspace_member base P.certificate.M _ (by unfold workspaceSize rowWidth;omega)
  have following : header.outputCursor+1∈workspace base P.certificate.M := by
    have equal : header.outputCursor+1=base+(16+2*rowWidth P.certificate.M+2+2*m) := by
      rw [cursor,length]
      unfold resultBase
      omega
    rw [equal]
    exact workspace_member base P.certificate.M _ (by unfold workspaceSize rowWidth;omega)
  have weightedFrame : Frame summed weighted base P.certificate.M :=
    ⟨fun address _outside => congrFun weightHeap address,fun address _outside => by rw [weightLive]⟩
  have emitFrame : Frame weighted after base P.certificate.M :=
    emit_frame weighted base P.certificate.M header.outputCursor (m+1) (P.cachedCappedError m) weight current following
  refine ⟨after,((sumRun.trans weightRun).trans emitRun).mono (by rw [level];omega),rfl,
    headerAfter,cacheAfter,?_,?_,(sumFrame.trans weightedFrame).trans emitFrame⟩
  · exact (emit_fresh weighted base header.outputCursor (m+1) (P.cachedCappedError m) weight).trans weightFresh
  · change weighted.output++[.rational (P.cachedCappedError m),.rational weight]=_
    rw [weightOutput,sumOutput,originalCalibration_pair P m bounded]

end PDLower.CalibrationCompute
