module

public import Paid.PDROC_CalibrationRow_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem scatterLoop (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (position : before.pc=labelAddress origin .scatterGate)
    (cursorBound : cursor≤2*level+1) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (1320*(2*level+1-cursor)+135) ∧
      ScatterData P base level clock (2*level+1) read write after ∧ after.pc=labelAddress origin .stepNext ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  have go (remaining : ℕ) : ∀ cursor before,2*level+1-cursor=remaining →
      cursor≤2*level+1 → ScatterData P base level clock cursor read write before →
      before.pc=labelAddress origin .scatterGate →
      ∃ after : State,Segment origin input before after (1320*(2*level+1-cursor)+135) ∧
        ScatterData P base level clock (2*level+1) read write after ∧ after.pc=labelAddress origin .stepNext ∧
        MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
        after.register .fresh=before.register .fresh := by
    induction remaining with
    | zero =>
      intro cursor before remainingEq cursorBound data position
      have equal : cursor=2*level+1 := by omega
      subst cursor
      let middle := gateResult before base 7 8 (2*level+1) (2*level+1)
      let after : State := {middle with pc:=labelAddress origin .stepNext}
      have body : linearExecute input (basicBlock .scatterGate).body before=some middle := by
        rw [scatterGate_body]
        exact gate_execute input before base 7 8 (2*level+1) (2*level+1) data.control.header.fresh
          (data.control.header.live 7 (by decide)) (data.control.header.live 8 (by decide))
          data.control.cursorValue data.control.width
      have control : (controlInstruction origin (basicBlock .scatterGate).control).execute input middle=some after := by
        simpa only [basicBlock,lt_self_iff_false,ite_false,middle,after] using
          gate_control_execute input before base 7 8 (2*level+1) (2*level+1) origin .stepNext .leftRead
      have run : Segment origin input before after 135 :=
        kernel_block_trace origin .scatterGate input before middle after position body control
      have fields := gate_fields before base 7 8 (2*level+1) (2*level+1) data.control.cursorValue data.control.width
      refine ⟨after,?_,ScatterData.sameMemory P base level clock (2*level+1) read write before after data rfl rfl fields.2.2.1,
        rfl,⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,fields.2.2.1⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_add] using run
    | succ remaining ih =>
      intro cursor before remainingEq cursorBound data position
      have inside : cursor<2*level+1 := by omega
      obtain ⟨next,firstRun,nextData,nextPosition,firstFrame,firstOutput,firstFresh⟩ :=
        scatterIteration input P origin base level clock cursor read write inside before data position levelBound
      obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
        ih (cursor+1) next (by omega) (by omega) nextData nextPosition
      have cost : 1320+(1320*(2*level+1-(cursor+1))+135)=1320*(2*level+1-cursor)+135 := by omega
      exact ⟨after,cost ▸ firstRun.trans run,done,last,firstFrame.trans frame,
        output.trans firstOutput,fresh.trans firstFresh⟩
  exact go (2*level+1-cursor) cursor before rfl cursorBound data position

/-- The completed physical destination is the original next walk row;
the real clock remains clock and the read/write orientation is unchanged
until the separately proved actual stepNext block performs its swap. -/
theorem scatter_complete (input : List Cell) (P : Parameters)
    (origin base level clock read write : ℕ) (before : State)
    (data : ScatterData P base level clock 0 read write before)
    (position : before.pc=labelAddress origin .scatterGate) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (3000*(level+1)) ∧
      ScatterData P base level clock (2*level+1) read write after ∧ after.pc=labelAddress origin .stepNext ∧
      RowAt after write (P.walkRow level true (clock+1)) ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
    scatterLoop input P origin base level clock 0 read write before data position (by omega) levelBound
  have completed : RowAt after write (P.walkRow level true (clock+1)) := by
    have stored := done.writeRow
    rw [rowScatterPrefix_complete] at stored
    exact stored
  exact ⟨after,run.mono (by omega),done,last,completed,frame,output,fresh⟩

end PDROC.CalibrationRow
