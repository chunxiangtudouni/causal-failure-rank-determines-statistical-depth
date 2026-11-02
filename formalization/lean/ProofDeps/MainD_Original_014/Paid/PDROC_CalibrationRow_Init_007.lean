module

public import Paid.PDROC_CalibrationRow_Init_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem initLoop (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (before : State) (data : InitData P base level cursor before)
    (position : before.pc=labelAddress origin .initGate)
    (cursorBound : cursor≤2*level+1) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (600*(2*level+1-cursor)+135) ∧
      InitData P base level (2*level+1) after ∧ after.pc=labelAddress origin .stepStart ∧
      MemoryFrame (region base P.certificate.M) before after ∧
      after.output=before.output ∧ after.register .fresh=before.register .fresh := by
  have go (remaining : ℕ) : ∀ cursor before,2*level+1-cursor=remaining →
      cursor≤2*level+1 → InitData P base level cursor before →
      before.pc=labelAddress origin .initGate →
      ∃ after : State,Segment origin input before after (600*(2*level+1-cursor)+135) ∧
        InitData P base level (2*level+1) after ∧ after.pc=labelAddress origin .stepStart ∧
        MemoryFrame (region base P.certificate.M) before after ∧
        after.output=before.output ∧ after.register .fresh=before.register .fresh := by
    induction remaining with
    | zero =>
      intro cursor before remainingEq cursorBound data position
      have equal : cursor=2*level+1 := by omega
      subst cursor
      let middle := gateResult before base 7 8 (2*level+1) (2*level+1)
      let after : State := {middle with pc:=labelAddress origin .stepStart}
      have body : linearExecute input (basicBlock .initGate).body before=some middle := by
        rw [initGate_body]
        exact gate_execute input before base 7 8 (2*level+1) (2*level+1) data.header.fresh
          (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
      have control : (controlInstruction origin (basicBlock .initGate).control).execute input middle=some after := by
        simpa only [basicBlock,lt_self_iff_false,ite_false,middle,after] using
          gate_control_execute input before base 7 8 (2*level+1) (2*level+1) origin .stepStart .initCell
      have run : Segment origin input before after 135 :=
        kernel_block_trace origin .initGate input before middle after position body control
      have fields := gate_fields before base 7 8 (2*level+1) (2*level+1) data.cursorValue data.width
      refine ⟨after,?_,InitData.sameMemory P base level (2*level+1) before after data rfl rfl fields.2.2.1,rfl,?_,rfl,fields.2.2.1⟩
      · simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_add] using run
      · exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
    | succ remaining ih =>
      intro cursor before remainingEq cursorBound data position
      have inside : cursor<2*level+1 := by omega
      let next := initIteration origin before base level cursor
      have iteration := initIteration_correct P origin base level cursor input before data position inside levelBound
      obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
        ih (cursor+1) next (by omega) (by omega) iteration.2.1 iteration.2.2
      have combined := iteration.1.trans run
      have cost : 600+(600*(2*level+1-(cursor+1))+135)=600*(2*level+1-cursor)+135 := by omega
      have widthInside : cursor<rowWidth P.certificate.M :=
        inside.trans_le (activeWidth_le P.certificate.M level levelBound)
      have firstFrame := initIteration_frame origin base P.certificate.M level cursor before data.cursorValue widthInside
      have preserved := initIteration_preserved origin base level cursor before data.cursorValue
      exact ⟨after,cost ▸ combined,done,last,firstFrame.trans frame,
        output.trans preserved.1,fresh.trans preserved.2⟩
  exact go (2*level+1-cursor) cursor before rfl cursorBound data position

/-- The complete literal initialization loop starts with NO assumed
row cells. It terminates at stepStart with the original delta row and
the actual natural terminal cursor, retaining all sixteen header cells. -/
theorem init_complete (P : Parameters) (origin base level : ℕ) (input : List Cell) (before : State)
    (header : Header P base level before)
    (position : before.pc=labelAddress origin .initGate)
    (cursor : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1))
    (read : before.heap (base+9)=.natural (firstRow base))
    (write : before.heap (base+10)=.natural (secondRow base P.certificate.M))
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (1600*(level+1)) ∧
      after.pc=labelAddress origin .stepStart ∧ Header P base level after ∧
      after.heap (base+7)=.natural (2*level+1) ∧
      after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (firstRow base) ∧
      after.heap (base+10)=.natural (secondRow base P.certificate.M) ∧
      RowAt after (firstRow base) (P.walkRow level true 0) ∧
      MemoryFrame (region base P.certificate.M) before after ∧
      after.output=before.output ∧ after.register .fresh=before.register .fresh := by
  have initial : InitData P base level 0 before :=
    ⟨header,cursor,width,read,write,RowPrefix.zero before (firstRow base) (P.walkRow level true 0)⟩
  obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
    initLoop P origin base level 0 input before initial position (by omega) levelBound
  exact ⟨after,run.mono (by omega),last,done.header,done.cursorValue,done.width,done.read,done.write,
    InitData.complete P base level after done,frame,output,fresh⟩

end PDROC.CalibrationRow
