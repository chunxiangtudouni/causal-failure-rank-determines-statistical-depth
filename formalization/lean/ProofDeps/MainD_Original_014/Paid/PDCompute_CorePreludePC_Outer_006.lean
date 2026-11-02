module

public import Paid.PDCompute_CorePreludePC_PostRow_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

theorem finish_return_pc (origin : ℕ) (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (position : before.pc=labelAddress origin .finish)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (returnAbove : origin+1≤header.returnPC) :
    ScopedSegment origin input before {finishResult before base header.M with pc:=header.returnPC} 255 := by
  have ret:=represented.lookup (offset:=0) (value:=.natural header.returnPC) rfl
  simp only [Nat.add_zero] at ret
  exact scoped_block origin .finish input before (finishResult before base header.M) _ position
    (finish_execute input before base header represented fresh) (by
      simp [basicBlock,controlInstruction,Instruction.execute,finishResult,loadSlotResult,ret.1,Cell.nat?])
    (label_after_enter origin .finish (by decide)) returnAbove

theorem levelGate_continue_pc (origin : ℕ) (input : List Cell) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .levelGate)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (bounded : header.level≤header.M+1) :
    ∃ after : State,ScopedSegment origin input before after 165 ∧
      after.pc=labelAddress origin .levelInit ∧ header.At after base ∧
      after.register .fresh=.natural base ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let middle := levelGateResult before base header.level header.M
  let after : State := {middle with pc:=labelAddress origin .levelInit}
  have gate := scoped_branch origin .levelGate .finish .levelInit input before middle
    (header.level≤header.M+1) position (levelGate_execute input before base header represented fresh)
      rfl (by simp [middle,levelGateResult])
  have budget : 15*((basicBlock .levelGate).body.length+1)+15=165 := by decide
  refine ⟨after,?_,rfl,represented,?_,rfl,rfl,rfl⟩
  · simpa only [ite_eq_left bounded,budget] using gate
  · exact (levelGate_fresh before base header.level header.M).trans fresh

/-- The real final outer test falls through to the original indirect
return. All seven registers' required ABI fields are obtained by loads;
the heap, live set and existing output remain physically identical. -/
theorem levelGate_finish_pc (origin : ℕ) (input : List Cell) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .levelGate)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (finished : header.M+1<header.level) (returnAbove : origin+1≤header.returnPC) :
    ∃ after : State,ScopedSegment origin input before after 420 ∧
      after.pc=header.returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural header.returnPC ∧
      after.register .address=.natural (resultBase base header.M) ∧
      after.register .index=.natural (rowWidth header.M) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let middle := levelGateResult before base header.level header.M
  let branch : State := {middle with pc:=labelAddress origin .finish}
  have gate := scoped_branch origin .levelGate .finish .levelInit input before middle
    (header.level≤header.M+1) position (levelGate_execute input before base header represented fresh)
      rfl (by simp [middle,levelGateResult])
  have budget : 15*((basicBlock .levelGate).body.length+1)+15=165 := by decide
  have branchRun : ScopedSegment origin input before branch 165 := by
    simpa only [ite_eq_right (by omega : ¬header.level≤header.M+1),budget] using gate
  have branchHeader : header.At branch base := represented
  have branchFresh : branch.register .fresh=.natural base :=
    (levelGate_fresh before base header.level header.M).trans fresh
  let after : State := {finishResult branch base header.M with pc:=header.returnPC}
  have finishRun : ScopedSegment origin input branch after 255 :=
    finish_return_pc origin input branch base header rfl branchHeader branchFresh returnAbove
  have registers := finish_registers branch base header branchHeader branchFresh
  exact ⟨after,branchRun.trans finishRun,rfl,registers.2.1,registers.1,registers.2.2.1,
    registers.2.2.2,rfl,rfl,rfl⟩

/-- One genuine outer iteration, including the actual gate, complete
original Q-row, summation, endpoint weight calculation and two emissions. -/
theorem outerStep_pc (P : Parameters) (origin base endpoints returnPC count : ℕ) (input : List Cell)
    (before : State) (header : Header) (ready : OuterReady P base endpoints returnPC count header before)
    (position : before.pc=labelAddress origin .levelGate) (bounded : count<P.certificate.M+1)
    (separate : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+index∉workspace base P.certificate.M) :
    ∃ (after : State) (afterHeader : Header),ScopedSegment origin input before after (13000*(P.certificate.Q+1)*(count+2)) ∧
      after.pc=labelAddress origin .levelGate ∧ OuterReady P base endpoints returnPC (count+1) afterHeader after ∧
      after.output=before.output++encodeCalibration
        ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using bounded)) ∧
      Frame before after base P.certificate.M := by
  obtain ⟨entered,gateRun,gatePC,gateHeader,gateFresh,gateHeap,gateLive,gateOutput⟩ :=
    levelGate_continue_pc origin input base before header position ready.represented ready.fresh
      (by rw [ready.M,ready.level]; omega)
  have gateEndpoint : HeapList entered endpoints (encodeList encodeEndpoint P.endpointCache.toList) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.endpointHeap
  have gateCache : HeapList entered (resultBase base P.certificate.M) (calibrationPrefix P count) := by
    simpa only [HeapList,heapSegment,gateHeap,gateLive] using ready.cache
  obtain ⟨rowState,rowRun,rowPC,rowHeader,rowAt,rowFresh,rowOutput,rowMemory⟩ :=
    rowCall_pc P origin base input entered header gateHeader gateFresh ready.M ready.Q ready.gamma gatePC
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
    postRow_pc origin input P base count rowState rowHeaderValue rowPC rowHeader actualRow rowFresh
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

/-- All original M+1 levels, followed by the actual terminating test and
indirect return. The result cache and appended output are the original
full encoded calibration list; no successful callee is a hypothesis. -/
theorem outerLoop_pc (P : Parameters) (origin base endpoints returnPC count : ℕ) (input : List Cell)
    (before : State) (header : Header) (ready : OuterReady P base endpoints returnPC count header before)
    (position : before.pc=labelAddress origin .levelGate) (bounded : count≤P.certificate.M+1)
    (returnAbove : origin+1≤returnPC)
    (separate : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+index∉workspace base P.certificate.M) :
    ∃ (after : State) (extra : List Cell),
      ScopedSegment origin input before after (13000*(P.certificate.Q+1)*(P.certificate.M+2)*(P.certificate.M+1-count)+420) ∧
      OuterDone P base returnPC count before after extra := by
  let perLevel := 13000*(P.certificate.Q+1)*(P.certificate.M+2)
  have go (remaining : ℕ) : ∀ (count : ℕ) (before : State) (header : Header),
      P.certificate.M+1-count=remaining → count≤P.certificate.M+1 →
      OuterReady P base endpoints returnPC count header before → before.pc=labelAddress origin .levelGate →
      ∃ (after : State) (extra : List Cell),ScopedSegment origin input before after (perLevel*(P.certificate.M+1-count)+420) ∧
        OuterDone P base returnPC count before after extra := by
    induction remaining with
    | zero =>
      intro count before header distance bounded ready position
      have equal : count=P.certificate.M+1 := by omega
      obtain ⟨after,actual,pc,fresh,old,address,index,heap,live,output⟩ :=
        levelGate_finish_pc origin input base before header position ready.represented ready.fresh
          (by rw [ready.M,ready.level,equal]; omega) (by simpa only [ready.returnAddress] using returnAbove)
      have cache : HeapList after (resultBase base P.certificate.M)
          (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) := by
        simpa only [HeapList,heapSegment,heap,live,equal,calibrationPrefix_full] using ready.cache
      refine ⟨after,[],actual.mono (by rw [distance]; omega),?_,?_,?_,?_,?_,cache,?_,?_,?_⟩
      · exact pc.trans ready.returnAddress
      · exact fresh
      · simpa only [ready.returnAddress] using old
      · simpa only [ready.M] using address
      · simpa only [ready.M] using index
      · simpa only [List.append_nil] using output
      · simp only [equal,List.append_nil,calibrationPrefix_full]
      · exact ⟨fun query _outside => congrFun heap query,fun query _outside => by rw [live]⟩
    | succ remaining ih =>
      intro count before header distance bounded ready position
      have inside : count<P.certificate.M+1 := by omega
      obtain ⟨next,nextHeader,stepRun,nextPC,nextReady,stepOutput,stepFrame⟩ :=
        outerStep_pc P origin base endpoints returnPC count input before header ready position inside separate
      obtain ⟨after,extra,restRun,pc,fresh,old,address,index,cache,output,completion,restFrame⟩ :=
        ih (count+1) next nextHeader (by omega) (by omega) nextReady nextPC
      have cost : 13000*(P.certificate.Q+1)*(count+2)≤perLevel :=
        Nat.mul_le_mul_left (13000*(P.certificate.Q+1)) (by omega)
      have distanceStep : P.certificate.M+1-count=(P.certificate.M+1-(count+1))+1 := by omega
      have joined := (stepRun.mono cost).trans restRun
      have budget : perLevel+(perLevel*(P.certificate.M+1-(count+1))+420)=
          perLevel*(P.certificate.M+1-count)+420 := by
        rw [distanceStep]
        ring
      refine ⟨after,encodeCalibration ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using inside))++extra,
        budget ▸ joined,pc,fresh,old,address,index,cache,?_,?_,stepFrame.trans restFrame⟩
      · rw [output,stepOutput,List.append_assoc]
      · rw [←List.append_assoc,←calibrationPrefix_succ P count inside]
        exact completion
  exact go (P.certificate.M+1-count) count before header rfl bounded ready position


end PDCompute.CorePreludePC
