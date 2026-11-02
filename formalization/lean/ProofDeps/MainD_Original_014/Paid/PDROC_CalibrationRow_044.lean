module

public import Paid.PDROC_CalibrationRow_043
public import Paid.PDROC_CalibrationRow_014
public import Paid.PDROC_CalibrationRow_Init_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem rowCost_bound (Q level : ℕ) :
    480+1600*(level+1)+90+(5000*(Q-0)*(level+1)+135)≤10000*(Q+1)*(level+1) := by
  have initialCost : 480+1600*(level+1)+90+135≤10000*(level+1) := by omega
  have loopCost : 5000*Q*(level+1)≤10000*Q*(level+1) :=
    Nat.mul_le_mul_right (level+1) (Nat.mul_le_mul_right Q (by decide : 5000≤10000))
  calc
    _ = 5000*Q*(level+1)+(480+1600*(level+1)+90+135) := by simp only [Nat.sub_zero]; ring
    _ ≤ 5000*Q*(level+1)+10000*(level+1) := Nat.add_le_add_left initialCost _
    _ ≤ 10000*Q*(level+1)+10000*(level+1) := Nat.add_le_add_right loopCost _
    _ = 10000*(Q+1)*(level+1) := by ring

/-- Original local callee, from real levelInit through the real Q loop
to sumStart. Initial clock/cursor/width/pointers/row contents are NOT
premises. The terminal physical orientation is the exact Q-swap pair.
This is the execution/time/final-frame layer; full-prefix provenance is
composed separately rather than inferred from the terminal RowAt. -/
theorem row_complete (input : List Cell) (P : Parameters) (origin base level : ℕ) (before : State)
    (header : Header P base level before) (position : before.pc=labelAddress origin .levelInit)
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (10000*(P.certificate.Q+1)*(level+1)) ∧
      after.pc=labelAddress origin .sumStart ∧ StepData P base level P.certificate.Q after ∧
      after.heap (base+6)=.natural P.certificate.Q ∧ after.heap (base+7)=.natural (2*level+1) ∧
      after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (rowPointers base P.certificate.M P.certificate.Q).1 ∧
      after.heap (base+10)=.natural (rowPointers base P.certificate.M P.certificate.Q).2 ∧
      RowAt after (rowPointers base P.certificate.M P.certificate.Q).1 (P.walkRow level true P.certificate.Q) ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  let entry : State := {levelInitResult before base level P.certificate.M with pc:=labelAddress origin .initGate}
  obtain ⟨trace,head,last,chain,cost,_⟩ := levelInit_trace origin input P before base level header position
  have entryRun : Segment origin input before entry 480 := ⟨trace,head,last,chain,cost⟩
  have entryFrame : MemoryFrame (region base P.certificate.M) before entry := levelInit_frame before base level P.certificate.M
  have entryHeader := Header.transport P base level before entry header entryFrame
    (levelInit_live before base level P.certificate.M) (levelInit_fields before base level P.certificate.M).2.2.1
  have slots := levelInit_slots before base level P.certificate.M
  obtain ⟨initialized,initRun,initPosition,initHeader,initCursor,initWidth,initRead,initWrite,deltaRow,initFrame,initOutput,_⟩ :=
    init_complete P origin base level input entry entryHeader rfl slots.1 slots.2.1 slots.2.2.1 slots.2.2.2 levelBound
  let started := constantSlotResult initialized base 6 (.natural 0)
  let start : State := {started with pc:=labelAddress origin .stepGate}
  have startBody : linearExecute input (basicBlock .stepStart).body initialized=some started :=
    constantSlot_execute input initialized base 6 (.natural 0) initHeader.fresh
  have startControl : (controlInstruction origin (basicBlock .stepStart).control).execute input started=some start := rfl
  have startRun : Segment origin input initialized start 90 :=
    kernel_block_trace origin .stepStart input initialized started start initPosition startBody startControl
  have startDataMiddle := StepData.start P base level initialized initHeader initCursor initWidth initRead initWrite deltaRow
  have startData := StepData.sameMemory P base level 0 started start startDataMiddle rfl rfl rfl
  obtain ⟨after,qRun,done,finish,qFrame,qOutput,_⟩ :=
    qLoop input P origin base level 0 start startData rfl (Nat.zero_le _) levelBound
  have startFrame : MemoryFrame (region base P.certificate.M) initialized start :=
    constant_row_frame initialized base P.certificate.M 6 (.natural 0) (by decide) (by decide)
  have combined := ((entryRun.trans initRun).trans startRun).trans qRun
  have fullCost := rowCost_bound P.certificate.Q level
  refine ⟨after,combined.mono fullCost,finish,done,done.control.clockValue,done.control.cursorValue,done.control.width,
    done.control.read,done.control.write,done.readRow,((entryFrame.trans initFrame).trans startFrame).trans qFrame,
    ?_,done.control.header.fresh.trans header.fresh.symm⟩
  exact qOutput.trans initOutput

end PDROC.CalibrationRow
