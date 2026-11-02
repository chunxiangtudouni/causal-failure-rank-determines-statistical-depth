module

public import Paid.PDROC_CalibrationRow_049
public import Paid.PDROC_CalibrationRow_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem qIterationCost_bound (level : ℕ) :
    135+90+1000*(level+1)+90+3000*(level+1)+330≤5000*(level+1) := by omega

/-- One actual Q iteration on a SINGLE safe trace. Every zero/scatter
prefix keeps its canonical typed source, and each reset/swap prefix
keeps its concrete entry and literal execution. No closure or incoming
full-register operand bound is required. -/
theorem qIteration_provenance (input : List Cell) (P : Parameters) (origin base level clock : ℕ)
    (caller before : State) (previousProof : QProvenance P origin base level input caller before)
    (data : StepData P base level clock before) (position : before.pc=labelAddress origin .stepGate)
    (inside : clock<P.certificate.Q) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (QProvenance P origin base level input caller) before after (5000*(level+1)) ∧
      StepData P base level (clock+1) after ∧ after.pc=labelAddress origin .stepGate := by
  let Good := QProvenance P origin base level input caller
  have closed := qProvenance_closed P origin base level input caller
  let read := (rowPointers base P.certificate.M clock).1
  let write := (rowPointers base P.certificate.M clock).2
  let previous := P.walkRow level true clock
  have lower := Buffers.lower base P.certificate.M read write data.control.buffers
  let gate := gateResult before base 6 3 clock P.certificate.Q
  let zeroEntry : State := {gate with pc:=labelAddress origin .zeroStart}
  have gateFields := gate_fields before base 6 3 clock P.certificate.Q data.control.clockValue data.control.header.Q
  have gateBody : linearExecute input (basicBlock .stepGate).body before=some gate := by
    rw [stepGate_body]
    exact gate_execute input before base 6 3 clock P.certificate.Q data.control.header.fresh
      (data.control.header.live 6 (by decide)) (data.control.header.live 3 (by decide))
      data.control.clockValue data.control.header.Q
  have gateControl : (controlInstruction origin (basicBlock .stepGate).control).execute input gate=some zeroEntry := by
    simpa only [basicBlock,inside,ite_true,gate,zeroEntry] using
      gate_control_execute input before base 6 3 clock P.certificate.Q origin .sumStart .zeroStart
  have gateProvenance : ∀ state,BlockPrefix input .stepGate before zeroEntry state→Good state :=
    closed .stepGate before gate zeroEntry (.gate clock before inside.le data) previousProof position gateBody gateControl
  have gateRun : SafeSegment origin base (region base P.certificate.M) input Good before zeroEntry 135 := by
    apply SafeSegment.ofBlock origin base _ input Good .stepGate rfl before gate zeroEntry position gateBody gateControl
      (by simpa only [stepGate_body] using gate_prefix_frames (region base P.certificate.M) input before 6 3)
      data.control.header.live ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ gateFields.2.2.2.2.2.2.2 gateFields.2.2.1
      (fun _ member => member) gateProvenance
  have gateData := StepData.sameMemory P base level clock before zeroEntry data rfl rfl gateFields.2.2.1
  let zeroMiddle := constantSlotResult zeroEntry base 7 (.natural 0)
  let zeroGate : State := {zeroMiddle with pc:=labelAddress origin .zeroGate}
  have zeroBody : linearExecute input (basicBlock .zeroStart).body zeroEntry=some zeroMiddle :=
    constantSlot_execute input zeroEntry base 7 (.natural 0) gateData.control.header.fresh
  have zeroControl : (controlInstruction origin (basicBlock .zeroStart).control).execute input zeroMiddle=some zeroGate := rfl
  have zeroStartRun : SafeSegment origin base (region base P.certificate.M) input Good zeroEntry zeroGate 90 :=
    constantRow_safe input P origin base level 7 .zeroStart .zeroGate zeroEntry gateData.control.header rfl rfl rfl rfl
      (by decide) (by decide) Good
      (closed .zeroStart zeroEntry zeroMiddle zeroGate (.zeroStart clock zeroEntry inside gateData)
        gateRun.final.2.2.2.2 rfl zeroBody zeroControl)
  have zeroControls := RowControl.afterConstantCursor P base level clock (2*level+1) read write 0 zeroEntry gateData.control
  have zeroRead := constantHeader_preserves_row zeroEntry base 7 read (.natural 0) previous gateData.readRow (by decide) lower.1
  have zeroMiddleData : ZeroData P base level clock 0 read write previous zeroMiddle :=
    ⟨zeroControls.header,zeroControls.buffers,zeroControls.clockValue,zeroControls.cursorValue,zeroControls.width,
      zeroControls.read,zeroControls.write,PDROC.endpointWalkRow_size P level true clock,zeroRead,
      RowPrefix.zero zeroMiddle write (Array.replicate (2*level+1) (0 : ℚ))⟩
  have zeroInitial := ZeroData.sameMemory P base level clock 0 read write previous zeroMiddle zeroGate zeroMiddleData rfl rfl rfl
  obtain ⟨zeroDone,zeroRaw,zeroData,zeroPosition,zeroRow⟩ :=
    ZeroRuntime.complete_safe input P origin base level clock read write previous zeroGate
      (ZeroRuntime.ZeroProvenance P origin base level clock read write previous input zeroGate)
      (ZeroRuntime.provenance_closed input P origin base level clock read write previous zeroGate levelBound)
      zeroInitial.header zeroInitial.buffers (.initial zeroInitial) rfl zeroInitial.clockValue zeroInitial.cursorValue zeroInitial.width
      zeroInitial.readValue zeroInitial.writeValue zeroInitial.previousSize zeroInitial.readRow levelBound
  have zeroRun : SafeSegment origin base (region base P.certificate.M) input Good zeroGate zeroDone (1000*(level+1)) :=
    zeroRaw.weaken (fun state phase => QProvenance.zero clock zeroGate state zeroStartRun.final.2.2.2.2
      inside zeroInitial rfl phase)
  let scatterMiddle := constantSlotResult zeroDone base 7 (.natural 0)
  let scatterGate : State := {scatterMiddle with pc:=labelAddress origin .scatterGate}
  have scatterBody : linearExecute input (basicBlock .scatterStart).body zeroDone=some scatterMiddle :=
    constantSlot_execute input zeroDone base 7 (.natural 0) zeroData.header.fresh
  have scatterControl : (controlInstruction origin (basicBlock .scatterStart).control).execute input scatterMiddle=some scatterGate := rfl
  have scatterStartRun : SafeSegment origin base (region base P.certificate.M) input Good zeroDone scatterGate 90 :=
    constantRow_safe input P origin base level 7 .scatterStart .scatterGate zeroDone zeroData.header rfl zeroPosition rfl rfl
      (by decide) (by decide) Good
      (closed .scatterStart zeroDone scatterMiddle scatterGate (.scatterStart clock zeroDone inside zeroData zeroRow)
        zeroRun.final.2.2.2.2 zeroPosition scatterBody scatterControl)
  have beforeScatter : RowControl P base level clock (2*level+1) read write zeroDone :=
    ⟨zeroData.header,zeroData.buffers,zeroData.clockValue,zeroData.cursorValue,zeroData.width,zeroData.readValue,zeroData.writeValue⟩
  have scatterControls := RowControl.afterConstantCursor P base level clock (2*level+1) read write 0 zeroDone beforeScatter
  have scatterRead := constantHeader_preserves_row zeroDone base 7 read (.natural 0) previous zeroData.readRow (by decide) lower.1
  have scatterWrite := constantHeader_preserves_row zeroDone base 7 write (.natural 0)
    (Array.replicate (2*level+1) (0 : ℚ)) zeroRow (by decide) lower.2
  have scatterMiddleData : ScatterData P base level clock 0 read write scatterMiddle := by
    refine ⟨scatterControls,scatterRead,?_⟩
    simpa only [rowScatterPrefix_zero] using scatterWrite
  have scatterInitial := ScatterData.sameMemory P base level clock 0 read write scatterMiddle scatterGate scatterMiddleData rfl rfl rfl
  obtain ⟨scatterDone,scatterRaw,scatterData,scatterPosition,newRow,_,_,_⟩ :=
    scatter_complete_provenance input P origin base level clock read write scatterGate scatterInitial rfl levelBound
  have scatterRun : SafeSegment origin base (region base P.certificate.M) input Good scatterGate scatterDone (3000*(level+1)) :=
    scatterRaw.weaken (fun state phase => QProvenance.scatter clock scatterGate state
      scatterStartRun.final.2.2.2.2 inside scatterInitial rfl phase)
  let swapMiddle := stepNextResult scatterDone base clock
  let after : State := {swapMiddle with pc:=labelAddress origin .stepGate}
  have swapBody := stepNext_execute input scatterDone base clock scatterData.control.header.fresh
    (scatterData.control.header.live 6 (by decide)) scatterData.control.clockValue
    (scatterData.control.header.live 9 (by decide)) (scatterData.control.header.live 10 (by decide))
  have swapControl : (controlInstruction origin (basicBlock .stepNext).control).execute input swapMiddle=some after := rfl
  have swapRun : SafeSegment origin base (region base P.certificate.M) input Good scatterDone after 330 :=
    stepNext_safe input P origin base level clock read write scatterDone scatterData.control scatterPosition Good
      (closed .stepNext scatterDone swapMiddle after (.next clock scatterDone inside scatterData newRow)
        scatterRun.final.2.2.2.2 scatterPosition swapBody swapControl)
  have swapped := StepData.afterSwap input P base level clock scatterDone scatterData.control newRow
  have done := StepData.sameMemory P base level (clock+1) swapMiddle after swapped rfl rfl rfl
  have run := ((((gateRun.trans zeroStartRun).trans zeroRun).trans scatterStartRun).trans scatterRun).trans swapRun
  exact ⟨after,run.mono (qIterationCost_bound level),done,rfl⟩

end PDROC.CalibrationRow
