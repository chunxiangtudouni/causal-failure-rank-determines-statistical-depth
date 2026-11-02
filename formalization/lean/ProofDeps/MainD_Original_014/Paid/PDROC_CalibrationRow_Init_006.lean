module

public import Paid.PDROC_CalibrationRow_Init_005
public import Paid.PDROC_CalibrationRow_010
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def initGateToCell (origin : ℕ) (before : State) (base level cursor : ℕ) : State :=
  {gateResult before base 7 8 cursor (2*level+1) with pc:=labelAddress origin .initCell}

def initPick (origin : ℕ) (before : State) (base level cursor : ℕ) : State :=
  let gate := initGateToCell origin before base level cursor
  let cell := initCellNext origin gate base level cursor
  if cursor=level then initCenterNext origin cell else cell

theorem initPick_fields (origin : ℕ) (before : State) (base level cursor : ℕ)
    (cursorValue : before.heap (base+7)=.natural cursor) :
    (initPick origin before base level cursor).heap=before.heap ∧
    (initPick origin before base level cursor).live=before.live ∧
    (initPick origin before base level cursor).register .fresh=before.register .fresh ∧
    (initPick origin before base level cursor).register .index=.natural cursor ∧
    (initPick origin before base level cursor).register .value=.rational (if cursor=level then 1 else 0) ∧
    (initPick origin before base level cursor).pc=labelAddress origin .initStore ∧
    (initPick origin before base level cursor).output=before.output := by
  by_cases center : cursor=level <;>
    simp [initPick,initGateToCell,gateResult,initCellNext,initCellResult,
      initCenterNext,initCenterResult,loadSlotResult,State.set,center,cursorValue]

/-- The actual gate, cell comparison and optional centre constant have
all run before the row store. Both branch outcomes retain the same row. -/
theorem initPick_segment (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (before : State) (data : InitData P base level cursor before)
    (position : before.pc=labelAddress origin .initGate) (inside : cursor<2*level+1) :
    Segment origin input before (initPick origin before base level cursor) 300 := by
  let gate := initGateToCell origin before base level cursor
  let cell := initCellNext origin gate base level cursor
  have gateBody : linearExecute input (basicBlock .initGate).body before=
      some (gateResult before base 7 8 cursor (2*level+1)) := by
    rw [initGate_body]
    exact gate_execute input before base 7 8 cursor (2*level+1) data.header.fresh
      (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
  have gateControl : (controlInstruction origin (basicBlock .initGate).control).execute input
      (gateResult before base 7 8 cursor (2*level+1))=some gate := by
    simpa only [basicBlock,inside,ite_true,gate,initGateToCell] using
      gate_control_execute input before base 7 8 cursor (2*level+1) origin .stepStart .initCell
  have gateRun : Segment origin input before gate 135 :=
    kernel_block_trace origin .initGate input before (gateResult before base 7 8 cursor (2*level+1)) gate
      position gateBody gateControl
  have gateFields := gate_fields before base 7 8 cursor (2*level+1) data.cursorValue data.width
  obtain ⟨trace,head,last,_,chain,cost,_⟩ := initCell_trace origin input gate base level cursor rfl
    (gateFields.2.2.1.trans data.header.fresh) (data.header.live 5 (by decide)) data.header.level
    gateFields.2.2.2.1
  have cellRun : Segment origin input gate cell 105 := ⟨trace,head,last,chain,cost⟩
  have pair : Segment origin input before cell 240 := gateRun.trans cellRun
  by_cases center : cursor=level
  · have centerPC : cell.pc=labelAddress origin .initCenter := by
      simp only [cell,initCellNext,center,ite_true]
    obtain ⟨trace,head,last,_,chain,cost,_⟩ := initCenter_trace origin input cell centerPC
    have centerRun : Segment origin input cell (initCenterNext origin cell) 45 := ⟨trace,head,last,chain,cost⟩
    have whole := (pair.trans centerRun).mono (by decide : 240+45≤300)
    simpa only [initPick,center,ite_true,gate,cell] using whole
  · have whole := pair.mono (by decide : 240≤300)
    simpa only [initPick,center,ite_false,gate,cell] using whole

def initIteration (origin : ℕ) (before : State) (base level cursor : ℕ) : State :=
  initStoreNext origin (initPick origin before base level cursor) base cursor

theorem initIteration_frame (origin base M level cursor : ℕ) (before : State)
    (cursorValue : before.heap (base+7)=.natural cursor) (inside : cursor<rowWidth M) :
    MemoryFrame (region base M) before (initIteration origin before base level cursor) := by
  have fields := initPick_fields origin before base level cursor cursorValue
  have pickFrame : MemoryFrame (region base M) before (initPick origin before base level cursor) :=
    ⟨fun _ _ => congrFun fields.1 _,fun _ _ => by rw [fields.2.1]⟩
  exact pickFrame.trans (initStore_frame (initPick origin before base level cursor) base M cursor inside)

theorem initIteration_preserved (origin base level cursor : ℕ) (before : State)
    (cursorValue : before.heap (base+7)=.natural cursor) :
    (initIteration origin before base level cursor).output=before.output ∧
      (initIteration origin before base level cursor).register .fresh=before.register .fresh := by
  have pick := initPick_fields origin before base level cursor cursorValue
  have stored := initStore_fields (initPick origin before base level cursor) base cursor
  exact ⟨stored.2.2.2.2.2.trans pick.2.2.2.2.2.2,stored.2.2.1.trans pick.2.2.1⟩

theorem initIteration_correct (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (before : State) (data : InitData P base level cursor before)
    (position : before.pc=labelAddress origin .initGate) (inside : cursor<2*level+1)
    (levelBound : level≤P.certificate.M+1) :
    Segment origin input before (initIteration origin before base level cursor) 600 ∧
      InitData P base level (cursor+1) (initIteration origin before base level cursor) ∧
      (initIteration origin before base level cursor).pc=labelAddress origin .initGate := by
  let pick := initPick origin before base level cursor
  have fields := initPick_fields origin before base level cursor data.cursorValue
  have picked : InitData P base level cursor pick :=
    InitData.sameMemory P base level cursor before pick data fields.1 fields.2.1 fields.2.2.1
  obtain ⟨trace,head,last,_,chain,cost,_⟩ := initStore_trace origin input pick base cursor
    fields.2.2.2.2.2.1 picked.header.fresh (picked.header.live 9 (by decide)) picked.read
    (picked.header.live 7 (by decide)) picked.cursorValue fields.2.2.2.1
  have stored : Segment origin input pick (initStoreNext origin pick base cursor) 225 :=
    ⟨trace,head,last,chain,cost⟩
  have run := ((initPick_segment P origin base level cursor input before data position inside).trans stored).mono
    (by decide : 300+225≤600)
  exact ⟨run,InitData.advance_control P origin base level cursor pick picked inside levelBound fields.2.2.2.2.1,rfl⟩

end PDROC.CalibrationRow
