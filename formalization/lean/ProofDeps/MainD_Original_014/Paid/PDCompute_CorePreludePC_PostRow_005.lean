module

public import Paid.PDCompute_CorePreludePC_Sum_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

theorem row_scoped {origin base : ℕ} {input : List Cell} {region : Finset ℕ}
    {Good : State→Prop} {before after : State} {cost : ℕ}
    (actual : PDROC.CalibrationRow.SafeSegment origin base region input Good before after cost)
    (interpreted : ∀ state,Good state → origin+1≤state.pc) :
    ScopedSegment origin input before after cost := by
  obtain ⟨states,head,last,chain,time,properties⟩:=actual
  exact ⟨states,head,last,chain,time,fun state member=>interpreted state (properties state member).2.2.2.2⟩

/-- The original complete row and caller-header reconstruction, with
all PC facts interpreted on its SAME frozen canonical provenance trace. -/
theorem rowCall_pc (P : Parameters) (origin base : ℕ) (input : List Cell)
    (before : State) (header : PDLower.CalibrationCompute.Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (M : header.M=P.certificate.M) (Q : header.Q=P.certificate.Q)
    (gamma : header.gamma=P.certificate.gamma)
    (position : before.pc=labelAddress origin .levelInit) (bounded : header.level≤P.certificate.M+1) :
    ∃ after : State, ScopedSegment origin input before after (10000*(P.certificate.Q+1)*(header.level+1)) ∧
      after.pc=labelAddress origin .sumStart ∧
      ({header with
        clock:=P.certificate.Q,cursor:=2*header.level+1,width:=2*header.level+1,
        readBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1,
        writeBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2}).At after base ∧
      RowAt after (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
        (P.walkRow header.level true P.certificate.Q) ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧
      MemoryFrame (PDROC.CalibrationRow.region base P.certificate.M) before after := by
  have arguments:=represented.rowArguments fresh M Q gamma
  obtain ⟨after,actual,pc,data,clock,cursor,width,read,write,row⟩:=
    PDROC.CalibrationRow.row_complete_provenance input P origin base header.level before arguments position bounded
  have final:=actual.final
  have callerFrame : MemoryFrame (PDROC.CalibrationRow.region base header.M) before after:=by simpa only [M] using final.1
  have callerHeader:=represented.afterRow callerFrame final.2.2.2.1 _ _ _ _ _ clock cursor width read write
  exact ⟨after,row_scoped actual (fun state provenance=>row_provenance_lower P origin base header.level input before state position provenance),
    pc,callerHeader,row,final.2.2.1.trans fresh,final.2.1,final.1⟩

/-- The actual heap endpoint read, actual denominator branch, legal
division or zero branch, and actual jump to emit. No supplied weight or
successful weight-computation witness appears in the hypotheses. -/
theorem weightPhase_pc (origin : ℕ) (input : List Cell) (P : Parameters) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .weight)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (cache : HeapList before header.endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (positive : 0<header.level) (bounded : header.level≤P.certificate.M+1) :
    ∃ after : State,ScopedSegment origin input before after 400 ∧
      after.pc=labelAddress origin .emit ∧ header.At after base ∧
      after.register .fresh=.natural base ∧
      after.register .value=.rational (computedWeight (P.endpointConstant (header.level-1)).error header.q) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let error := (P.endpointConstant (header.level-1)).error
  let middle := weightResult before base header.endpoints header.level error header.q
  have endpoint := represented.lookup (offset:=1) (value:=.natural header.endpoints) rfl
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have q := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have actualError := endpointHeap_error cache positive bounded
  have literal := weight_execute input before base header.endpoints header.level error header.q fresh
    endpoint.2 endpoint.1 level.2 level.1 q.2 q.1 actualError.1 actualError.2
  have gate := scoped_branch origin .weight .divide .zeroWeight input before middle
    ((1/2-header.q : ℚ)=0) position literal rfl (by simp [middle,weightResult])
  by_cases zero : (1/2-header.q : ℚ)=0
  · let branch : State := {middle with pc:=labelAddress origin .zeroWeight}
    let completed := ({branch with pc:=branch.pc+1}).set .value (.rational 0)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have budget : 15*((basicBlock .weight).body.length+1)+15=330 := by decide
    have branchRun : ScopedSegment origin input before branch 330 := by simpa only [ite_eq_left zero,budget] using gate
    have finish : ScopedSegment origin input branch after 45 :=
      scoped_go origin .zeroWeight .emit input branch completed rfl (zeroWeight_execute input branch) rfl
    refine ⟨after,(branchRun.trans finish).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,weightResult,weightLoaded,loadSlotResult,State.set] using fresh
    · simp only [after,completed,State.set,Function.update_self,computedWeight,ite_eq_left zero]
  · let branch : State := {middle with pc:=labelAddress origin .divide}
    let completed := divideResult branch (1/2-error) (1/2-header.q)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have budget : 15*((basicBlock .weight).body.length+1)+15=330 := by decide
    have branchRun : ScopedSegment origin input before branch 330 := by simpa only [ite_eq_right zero,budget] using gate
    have total : branch.register .total=.rational (1/2-error) := by
      simp [branch,middle,weightResult,weightLoaded,loadSlotResult]
    have value : branch.register .value=.rational (1/2-header.q) := by simp [branch,middle,weightResult]
    have finish : ScopedSegment origin input branch after 45 :=
      scoped_go origin .divide .emit input branch completed rfl
        (divide_execute input branch (1/2-error) (1/2-header.q) total value zero) rfl
    refine ⟨after,(branchRun.trans finish).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,divideResult,weightResult,weightLoaded,loadSlotResult] using fresh
    · simp only [after,completed,divideResult,Function.update_self,computedWeight,ite_eq_right zero,error]

/-- Actual outer-cache extension with the complete original workspace
frame. This consumes a physical row, never a supplied q/weight/run. -/
theorem postRow_pc (origin : ℕ) (input : List Cell) (P : Parameters) (base m : ℕ)
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
    ∃ after : State,ScopedSegment origin input before after (2000*(m+2)) ∧
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
    sumPhase_pc origin input base (P.walkRow (m+1) true P.certificate.Q)
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
    weightPhase_pc origin input P base summed summedHeader sumPC summedRepresented sumFresh endpointCache
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
  have emitRun : ScopedSegment origin input weighted after 390 :=
    scoped_go origin .emit .levelGate input weighted completed weightPC body rfl
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


end PDCompute.CorePreludePC
