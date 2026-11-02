module

public import Paid.PDROC_CalibrationRow_035
public import Paid.PDROC_CalibrationRow_036
public import Paid.PDROC_CalibrationRow_033
public import Paid.PDROC_CalibrationRow_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- One genuine original source-cell cycle: gate, both channel reads,
their actual absorbing/interior branches, TWO sequential stores, and
only then the true cursor increment. -/
theorem scatterIteration (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (position : before.pc=labelAddress origin .scatterGate) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after 1320 ∧
      ScatterData P base level clock (cursor+1) read write after ∧ after.pc=labelAddress origin .scatterGate ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let start : State := {gate with pc:=labelAddress origin .leftRead}
  have gateFields := gate_fields before base 7 8 cursor (2*level+1) data.control.cursorValue data.control.width
  have gateBody : linearExecute input (basicBlock .scatterGate).body before=some gate := by
    rw [scatterGate_body]
    exact gate_execute input before base 7 8 cursor (2*level+1) data.control.header.fresh
      (data.control.header.live 7 (by decide)) (data.control.header.live 8 (by decide))
      data.control.cursorValue data.control.width
  have gateControl : (controlInstruction origin (basicBlock .scatterGate).control).execute input gate=some start := by
    simpa only [basicBlock,inside,ite_true,gate,start] using
      gate_control_execute input before base 7 8 cursor (2*level+1) origin .stepNext .leftRead
  have gateRun : Segment origin input before start 135 :=
    kernel_block_trace origin .scatterGate input before gate start position gateBody gateControl
  have startData := ScatterData.sameMemory P base level clock cursor read write before start data rfl rfl gateFields.2.2.1
  obtain ⟨leftReady,leftReadRun,leftData,leftPosition,leftIndex,leftValue,leftHeap,leftLive,leftOutput,_⟩ :=
    leftRoute input P origin base level clock cursor read write inside start startData rfl gateFields.2.2.2.1
  have leftCorrect := leftStore_correct input P base level clock cursor read write leftReady leftData inside levelBound leftIndex leftValue
  let leftMiddle := leftStoreResult P leftReady base level clock cursor write inside
  let leftDone : State := {leftMiddle with pc:=labelAddress origin .rightRead}
  have leftControl : (controlInstruction origin (basicBlock .leftStore).control).execute input leftMiddle=some leftDone := rfl
  have leftStoreRun : Segment origin input leftReady leftDone 135 :=
    kernel_block_trace origin .leftStore input leftReady leftMiddle leftDone leftPosition leftCorrect.1 leftControl
  have afterLeft := ScatterLeftData.sameMemory P base level clock cursor read write inside leftMiddle leftDone leftCorrect.2 rfl rfl rfl
  obtain ⟨rightReady,rightReadRun,rightData,rightPosition,rightIndex,rightValue,rightHeap,rightLive,rightOutput,_⟩ :=
    rightRoute input P origin base level clock cursor read write inside leftDone afterLeft rfl
  have rightCorrect := rightStore_correct input P base level clock cursor read write inside rightReady rightData levelBound rightIndex rightValue
  let rightMiddle := rightStoreResult P rightReady base level clock cursor write inside
  let nextEntry : State := {rightMiddle with pc:=labelAddress origin .scatterNext}
  have rightControl : (controlInstruction origin (basicBlock .rightStore).control).execute input rightMiddle=some nextEntry := rfl
  have rightStoreRun : Segment origin input rightReady nextEntry 135 :=
    kernel_block_trace origin .rightStore input rightReady rightMiddle nextEntry rightPosition rightCorrect.1 rightControl
  have afterRight := ScatterBothData.sameMemory P base level clock cursor read write rightMiddle nextEntry rightCorrect.2 rfl rfl rfl
  have nextCorrect := scatterNext_correct input P base level clock cursor read write nextEntry afterRight
  let after : State := {incrementSlotResult nextEntry base 7 cursor with pc:=labelAddress origin .scatterGate}
  have nextControl : (controlInstruction origin (basicBlock .scatterNext).control).execute input
      (incrementSlotResult nextEntry base 7 cursor)=some after := rfl
  have nextRun : Segment origin input nextEntry after 150 :=
    kernel_block_trace origin .scatterNext input nextEntry (incrementSlotResult nextEntry base 7 cursor) after rfl nextCorrect.1 nextControl
  have done := ScatterData.sameMemory P base level clock (cursor+1) read write
    (incrementSlotResult nextEntry base 7 cursor) after nextCorrect.2 rfl rfl rfl
  have leftTargetBound : (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  have rightTargetBound : (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  have leftFrame : MemoryFrame (region base P.certificate.M) leftReady leftDone := by
    let target := (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
    let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
    let amount := (P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma)
    have fields := scatterStore_fields leftReady base write target (previous.getD target 0) amount
    exact frame_of_one_update _ leftReady leftDone (write+target) (.rational (previous.getD target 0+amount))
      (Buffers.write_mem base P.certificate.M read write target data.control.buffers leftTargetBound) fields.1 fields.2.1
  have rightFrame : MemoryFrame (region base P.certificate.M) rightReady nextEntry := by
    let target := (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
    let previous := rowLeftPrefix P level clock cursor inside
    let amount := (P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma)
    have fields := scatterStore_fields rightReady base write target (previous.getD target 0) amount
    exact frame_of_one_update _ rightReady nextEntry (write+target) (.rational (previous.getD target 0+amount))
      (Buffers.write_mem base P.certificate.M read write target data.control.buffers rightTargetBound) fields.1 fields.2.1
  have nextFrame : MemoryFrame (region base P.certificate.M) nextEntry after := by
    apply frame_of_one_update _ nextEntry _ (base+7) (.natural (cursor+1))
      (header_mem_region base _ 7 (by decide) (by decide))
    · simp [after,incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult]
    · rfl
  have firstFrame : MemoryFrame (region base P.certificate.M) before leftReady :=
    ⟨fun address _ => congrFun leftHeap address,fun _ _ => by rw [leftLive]; rfl⟩
  have middleFrame : MemoryFrame (region base P.certificate.M) leftDone rightReady :=
    ⟨fun address _ => congrFun rightHeap address,fun _ _ => by rw [rightLive]⟩
  refine ⟨after,((((gateRun.trans leftReadRun).trans leftStoreRun).trans rightReadRun).trans rightStoreRun).trans nextRun,
    done,rfl,(((firstFrame.trans leftFrame).trans middleFrame).trans rightFrame).trans nextFrame,?_,
    done.control.header.fresh.trans data.control.header.fresh.symm⟩
  change rightReady.output=before.output
  exact rightOutput.trans leftOutput

end PDROC.CalibrationRow
