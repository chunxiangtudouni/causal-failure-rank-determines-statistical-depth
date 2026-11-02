module

public import Paid.PDROC_CalibrationRow_026
public import Paid.PDROC_CalibrationRow_010
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def zeroIteration (origin : ℕ) (before : State) (base level write cursor : ℕ) : State :=
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let entered : State := {gate with pc:=labelAddress origin .zeroCell}
  {zeroCellResult entered base write cursor with pc:=labelAddress origin .zeroGate}

theorem zeroIteration_correct (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (previous : Array ℚ) (before : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (position : before.pc=labelAddress origin .zeroGate)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1) :
    Segment origin input before (zeroIteration origin before base level write cursor) 375 ∧
      ZeroData P base level clock (cursor+1) read write previous (zeroIteration origin before base level write cursor) ∧
      (zeroIteration origin before base level write cursor).pc=labelAddress origin .zeroGate := by
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let entered : State := {gate with pc:=labelAddress origin .zeroCell}
  have fields := gate_fields before base 7 8 cursor (2*level+1) data.cursorValue data.width
  have gateBody : linearExecute input (basicBlock .zeroGate).body before=some gate := by
    rw [zeroGate_body]
    exact gate_execute input before base 7 8 cursor (2*level+1) data.header.fresh
      (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
  have gateControl : (controlInstruction origin (basicBlock .zeroGate).control).execute input gate=some entered := by
    simpa only [basicBlock,inside,ite_true,gate,entered] using
      gate_control_execute input before base 7 8 cursor (2*level+1) origin .scatterStart .zeroCell
  have gateRun : Segment origin input before entered 135 :=
    kernel_block_trace origin .zeroGate input before gate entered position gateBody gateControl
  have enteredData := ZeroData.sameMemory P base level clock cursor read write previous before entered data rfl rfl fields.2.2.1
  have index : entered.register .index=.natural cursor := fields.2.2.2.1
  have cellBody := zeroCell_execute input P entered base level read write cursor enteredData.header enteredData.buffers
    enteredData.writeValue enteredData.cursorValue index
  have cellControl : (controlInstruction origin (basicBlock .zeroCell).control).execute input
      (zeroCellResult entered base write cursor)=some (zeroIteration origin before base level write cursor) := rfl
  have cellRun : Segment origin input entered (zeroIteration origin before base level write cursor) 240 :=
    kernel_block_trace origin .zeroCell input entered (zeroCellResult entered base write cursor)
      (zeroIteration origin before base level write cursor) rfl cellBody cellControl
  have done := ZeroData.advance input P base level clock cursor read write previous entered enteredData inside levelBound index
  refine ⟨gateRun.trans cellRun,?_,rfl⟩
  exact ZeroData.sameMemory P base level clock (cursor+1) read write previous
    (zeroCellResult entered base write cursor) (zeroIteration origin before base level write cursor) done rfl rfl rfl

theorem zeroIteration_frame (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (previous : Array ℚ) (before : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1) :
    MemoryFrame (region base P.certificate.M) before (zeroIteration origin before base level write cursor) := by
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let entered : State := {gate with pc:=labelAddress origin .zeroCell}
  have fields := gate_fields before base 7 8 cursor (2*level+1) data.cursorValue data.width
  have enteredData := ZeroData.sameMemory P base level clock cursor read write previous before entered data rfl rfl fields.2.2.1
  have cellFrame := zeroCell_frame input P entered base level read write cursor enteredData.header enteredData.buffers
    enteredData.writeValue enteredData.cursorValue fields.2.2.2.1 (inside.trans_le (activeWidth_le _ _ levelBound))
  exact (show MemoryFrame (region base P.certificate.M) before entered from
    ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩).trans cellFrame

theorem zeroIteration_preserved (origin base level write cursor : ℕ) (before : State)
    (cursorValue : before.heap (base+7)=.natural cursor)
    (width : before.heap (base+8)=.natural (2*level+1)) :
    (zeroIteration origin before base level write cursor).output=before.output ∧
    (zeroIteration origin before base level write cursor).register .fresh=before.register .fresh := by
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let entered : State := {gate with pc:=labelAddress origin .zeroCell}
  have cellFields := zeroCell_fields entered base write cursor
  have gateFields := gate_fields before base 7 8 cursor (2*level+1) cursorValue width
  exact ⟨cellFields.2.2.2.2.2.trans gateFields.2.2.2.2.2.2.2,
    cellFields.2.2.1.trans gateFields.2.2.1⟩

end PDROC.CalibrationRow
