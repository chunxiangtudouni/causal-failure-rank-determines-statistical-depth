module

public import Paid.PDROC_CalibrationRow_041
public import Paid.PDROC_CalibrationRow_028
public import Paid.PDROC_CalibrationRow_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem Buffers.lower (base M read write : ℕ) (buffers : Buffers base M read write) :
    base+16≤read ∧ base+16≤write := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> constructor <;> omega

/-- A genuine whole Q-step: actual gate, actual zero loop, actual
two-letter scatter loop, then the real clock increment and pointer swap.
No destination row or successful recursive step is supplied as an oracle. -/
theorem qIteration (input : List Cell) (P : Parameters) (origin base level clock : ℕ) (before : State)
    (data : StepData P base level clock before) (position : before.pc=labelAddress origin .stepGate)
    (inside : clock<P.certificate.Q) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (5000*(level+1)) ∧
      StepData P base level (clock+1) after ∧ after.pc=labelAddress origin .stepGate ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
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
  have gateRun : Segment origin input before zeroEntry 135 :=
    kernel_block_trace origin .stepGate input before gate zeroEntry position gateBody gateControl
  have gateData := StepData.sameMemory P base level clock before zeroEntry data rfl rfl gateFields.2.2.1
  let zeroMiddle := constantSlotResult zeroEntry base 7 (.natural 0)
  let zeroGate : State := {zeroMiddle with pc:=labelAddress origin .zeroGate}
  have zeroBody : linearExecute input (basicBlock .zeroStart).body zeroEntry=some zeroMiddle :=
    constantSlot_execute input zeroEntry base 7 (.natural 0) gateData.control.header.fresh
  have zeroControl : (controlInstruction origin (basicBlock .zeroStart).control).execute input zeroMiddle=some zeroGate := rfl
  have zeroStartRun : Segment origin input zeroEntry zeroGate 90 :=
    kernel_block_trace origin .zeroStart input zeroEntry zeroMiddle zeroGate rfl zeroBody zeroControl
  have zeroControls := RowControl.afterConstantCursor P base level clock (2*level+1) read write 0 zeroEntry gateData.control
  have zeroRead := constantHeader_preserves_row zeroEntry base 7 read (.natural 0) previous gateData.readRow (by decide) lower.1
  have zeroMiddleData : ZeroData P base level clock 0 read write previous zeroMiddle :=
    ⟨zeroControls.header,zeroControls.buffers,zeroControls.clockValue,zeroControls.cursorValue,zeroControls.width,
      zeroControls.read,zeroControls.write,PDROC.endpointWalkRow_size P level true clock,zeroRead,
      RowPrefix.zero zeroMiddle write (Array.replicate (2*level+1) (0 : ℚ))⟩
  have zeroInitial := ZeroData.sameMemory P base level clock 0 read write previous zeroMiddle zeroGate zeroMiddleData rfl rfl rfl
  obtain ⟨zeroDone,zeroRun,zeroData,zeroPosition,zeroRow,zeroFrame,zeroOutput,_⟩ :=
    zero_complete input P origin base level clock read write previous zeroGate zeroInitial.header zeroInitial.buffers rfl
      zeroInitial.clockValue zeroInitial.cursorValue zeroInitial.width zeroInitial.readValue zeroInitial.writeValue
      zeroInitial.previousSize zeroInitial.readRow levelBound
  let scatterMiddle := constantSlotResult zeroDone base 7 (.natural 0)
  let scatterGate : State := {scatterMiddle with pc:=labelAddress origin .scatterGate}
  have scatterBody : linearExecute input (basicBlock .scatterStart).body zeroDone=some scatterMiddle :=
    constantSlot_execute input zeroDone base 7 (.natural 0) zeroData.header.fresh
  have scatterControl : (controlInstruction origin (basicBlock .scatterStart).control).execute input scatterMiddle=some scatterGate := rfl
  have scatterStartRun : Segment origin input zeroDone scatterGate 90 :=
    kernel_block_trace origin .scatterStart input zeroDone scatterMiddle scatterGate zeroPosition scatterBody scatterControl
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
  obtain ⟨scatterDone,scatterRun,scatterData,scatterPosition,newRow,scatterFrame,scatterOutput,_⟩ :=
    scatter_complete input P origin base level clock read write scatterGate scatterInitial rfl levelBound
  let swapMiddle := stepNextResult scatterDone base clock
  let after : State := {swapMiddle with pc:=labelAddress origin .stepGate}
  have swapBody := stepNext_execute input scatterDone base clock scatterData.control.header.fresh
    (scatterData.control.header.live 6 (by decide)) scatterData.control.clockValue
    (scatterData.control.header.live 9 (by decide)) (scatterData.control.header.live 10 (by decide))
  have swapControl : (controlInstruction origin (basicBlock .stepNext).control).execute input swapMiddle=some after := rfl
  have swapRun : Segment origin input scatterDone after 330 :=
    kernel_block_trace origin .stepNext input scatterDone swapMiddle after scatterPosition swapBody swapControl
  have swapped := StepData.afterSwap input P base level clock scatterDone scatterData.control newRow
  have done := StepData.sameMemory P base level (clock+1) swapMiddle after swapped rfl rfl rfl
  have gateFrame : MemoryFrame (region base P.certificate.M) before zeroEntry := ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
  have zeroStartFrame : MemoryFrame (region base P.certificate.M) zeroEntry zeroGate :=
    constant_row_frame zeroEntry base P.certificate.M 7 (.natural 0) (by decide) (by decide)
  have scatterStartFrame : MemoryFrame (region base P.certificate.M) zeroDone scatterGate :=
    constant_row_frame zeroDone base P.certificate.M 7 (.natural 0) (by decide) (by decide)
  have swapFrame : MemoryFrame (region base P.certificate.M) scatterDone after := by
    change MemoryFrame (region base P.certificate.M) scatterDone swapMiddle
    exact (stepNext_prefix_frames (region base P.certificate.M) input scatterDone base clock scatterData.control.header.fresh
      (scatterData.control.header.live 6 (by decide)) scatterData.control.clockValue
      (scatterData.control.header.live 9 (by decide)) (scatterData.control.header.live 10 (by decide))
      (header_mem_region base _ 6 (by decide) (by decide)) (header_mem_region base _ 9 (by decide) (by decide))
      (header_mem_region base _ 10 (by decide) (by decide))).final swapBody
  have run := ((((gateRun.trans zeroStartRun).trans zeroRun).trans scatterStartRun).trans scatterRun).trans swapRun
  refine ⟨after,run.mono (by omega),done,rfl,
    ((((gateFrame.trans zeroStartFrame).trans zeroFrame).trans scatterStartFrame).trans scatterFrame).trans swapFrame,
    ?_,done.control.header.fresh.trans data.control.header.fresh.symm⟩
  change scatterDone.output=before.output
  exact scatterOutput.trans zeroOutput

end PDROC.CalibrationRow
