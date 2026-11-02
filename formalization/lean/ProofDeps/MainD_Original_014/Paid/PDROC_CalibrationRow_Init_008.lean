module

public import Paid.PDROC_CalibrationRow_Init_006
public import Paid.PDROC_CalibrationRow_Init_SafeSegment_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Concrete entry facts for the four ORIGINAL initialization blocks.
In particular header6 is neither inspected nor assumed to be natural. -/
def InitLabelEntry (level cursor : ℕ) (label : Label) (before : State) : Prop :=
  label=.initGate ∨ (cursor<2*level+1 ∧ before.register .index=.natural cursor ∧
    (label=.initCell ∨ (label=.initCenter ∧ cursor=level) ∨
      (label=.initStore ∧ before.register .value=.rational (if cursor=level then 1 else 0))))

/-- A proof-side phase/provenance closure rule. The full row runtime can
instantiate Good by its actual labelled phase certificate. This is not
an operand bound or a supplied successful run for the original program. -/
def InitClosed (P : Parameters) (origin base level : ℕ) (input : List Cell) (Good : State→Prop) : Prop :=
  ∀ cursor label before middle after,InitData P base level cursor before → cursor≤2*level+1 →
    InitLabelEntry level cursor label before → Good before → before.pc=labelAddress origin label →
    linearExecute input (basicBlock label).body before=some middle →
    (controlInstruction origin (basicBlock label).control).execute input middle=some after →
    ∀ state,((∃ count≤(basicBlock label).body.length,
      linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) → Good state

theorem initBlock_safe (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (Good : State→Prop) (closed : InitClosed P origin base level input Good)
    (label : Label) (row : rowLabel label=true) (before middle after : State)
    (data : InitData P base level cursor before) (bound : cursor≤2*level+1)
    (entry : InitLabelEntry level cursor label before) (good : Good before)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames (region base P.certificate.M) input (basicBlock label).body before)
    (lastFrame : MemoryFrame (region base P.certificate.M) before after)
    (lastOutput : after.output=before.output) (lastFresh : after.register .fresh=before.register .fresh)
    (lastLive : before.live ⊆ after.live) :
    SafeSegment origin base (region base P.certificate.M) input Good before after
      (15*((basicBlock label).body.length+2)) :=
  SafeSegment.ofBlock origin base _ input Good label row before middle after position body control frames
    data.header.live lastFrame lastOutput lastFresh lastLive
    (closed cursor label before middle after data bound entry good position body control)

theorem initPick_safe (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (Good : State→Prop) (closed : InitClosed P origin base level input Good)
    (before : State) (data : InitData P base level cursor before) (good : Good before)
    (position : before.pc=labelAddress origin .initGate) (inside : cursor<2*level+1) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      (initPick origin before base level cursor) 300 := by
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
  have gateFields := gate_fields before base 7 8 cursor (2*level+1) data.cursorValue data.width
  have gateRun : SafeSegment origin base (region base P.certificate.M) input Good before gate 135 :=
    initBlock_safe P origin base level cursor input Good closed .initGate rfl before
      (gateResult before base 7 8 cursor (2*level+1)) gate data inside.le (Or.inl rfl) good position
      gateBody gateControl (by simpa only [initGate_body] using gate_prefix_frames (region base P.certificate.M) input before 7 8)
      ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ gateFields.2.2.2.2.2.2.2 gateFields.2.2.1 (fun _ member => member)
  have gateData : InitData P base level cursor gate :=
    InitData.sameMemory P base level cursor before gate data rfl rfl gateFields.2.2.1
  have cellBody := initCell_execute input gate base level cursor gateData.header.fresh
    (gateData.header.live 5 (by decide)) gateData.header.level gateFields.2.2.2.1
  have cellFields := initCell_fields gate base level cursor
  have cellRun : SafeSegment origin base (region base P.certificate.M) input Good gate cell 105 :=
    initBlock_safe P origin base level cursor input Good closed .initCell rfl gate
      (initCellResult gate base level cursor) cell gateData inside.le
      (Or.inr ⟨inside,gateFields.2.2.2.1,Or.inl rfl⟩) gateRun.final.2.2.2.2 rfl
      cellBody (initCell_control_execute origin input gate base level cursor)
      (initCell_prefix_frames _ input gate)
      (by change MemoryFrame _ gate (initCellResult gate base level cursor)
          exact (initCell_prefix_frames _ input gate).final cellBody)
      cellFields.2.2.2.2.2.2.2 cellFields.2.2.1 (fun _ member => member)
  have pair := gateRun.trans cellRun
  by_cases center : cursor=level
  · have cellData : InitData P base level cursor cell :=
      InitData.sameMemory P base level cursor gate cell gateData rfl rfl cellFields.2.2.1
    have centerPC : cell.pc=labelAddress origin .initCenter := by simp only [cell,initCellNext,center,ite_true]
    have centerFields := initCenter_fields cell
    have centerRun : SafeSegment origin base (region base P.certificate.M) input Good cell
        (initCenterNext origin cell) 45 :=
      initBlock_safe P origin base level cursor input Good closed .initCenter rfl cell (initCenterResult cell)
        (initCenterNext origin cell) cellData inside.le
        (Or.inr ⟨inside,cellFields.2.2.2.1.trans gateFields.2.2.2.1,Or.inr (Or.inl ⟨rfl,center⟩)⟩)
        cellRun.final.2.2.2.2 centerPC (initCenter_execute input cell)
        (initCenter_control_execute origin input cell) (initCenter_prefix_frames _ input cell)
        (by change MemoryFrame _ cell (initCenterResult cell)
            exact (initCenter_prefix_frames _ input cell).final (initCenter_execute input cell))
        centerFields.2.2.2.2.2.2 centerFields.2.2.1 (fun _ member => member)
    have whole := (pair.trans centerRun).mono (by decide : 135+105+45≤300)
    simpa only [initPick,center,ite_true,gate,cell] using whole
  · have whole := pair.mono (by decide : 135+105≤300)
    simpa only [initPick,center,ite_false,gate,cell] using whole

end PDROC.CalibrationRow
