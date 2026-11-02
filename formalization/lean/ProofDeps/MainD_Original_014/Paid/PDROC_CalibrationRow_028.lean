module

public import Paid.PDROC_CalibrationRow_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem zeroLoop (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write : ℕ) (previous : Array ℚ) (before : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (position : before.pc=labelAddress origin .zeroGate)
    (cursorBound : cursor≤2*level+1) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (375*(2*level+1-cursor)+135) ∧
      ZeroData P base level clock (2*level+1) read write previous after ∧
      after.pc=labelAddress origin .scatterStart ∧
      MemoryFrame (region base P.certificate.M) before after ∧
      after.output=before.output ∧ after.register .fresh=before.register .fresh := by
  have go (remaining : ℕ) : ∀ cursor before,2*level+1-cursor=remaining →
      cursor≤2*level+1 → ZeroData P base level clock cursor read write previous before →
      before.pc=labelAddress origin .zeroGate →
      ∃ after : State,Segment origin input before after (375*(2*level+1-cursor)+135) ∧
        ZeroData P base level clock (2*level+1) read write previous after ∧
        after.pc=labelAddress origin .scatterStart ∧
        MemoryFrame (region base P.certificate.M) before after ∧
        after.output=before.output ∧ after.register .fresh=before.register .fresh := by
    induction remaining with
    | zero =>
      intro cursor before remainingEq cursorBound data position
      have equal : cursor=2*level+1 := by omega
      subst cursor
      let middle := gateResult before base 7 8 (2*level+1) (2*level+1)
      let after : State := {middle with pc:=labelAddress origin .scatterStart}
      have body : linearExecute input (basicBlock .zeroGate).body before=some middle := by
        rw [zeroGate_body]
        exact gate_execute input before base 7 8 (2*level+1) (2*level+1) data.header.fresh
          (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
      have control : (controlInstruction origin (basicBlock .zeroGate).control).execute input middle=some after := by
        simpa only [basicBlock,lt_self_iff_false,ite_false,middle,after] using
          gate_control_execute input before base 7 8 (2*level+1) (2*level+1) origin .scatterStart .zeroCell
      have run : Segment origin input before after 135 :=
        kernel_block_trace origin .zeroGate input before middle after position body control
      have fields := gate_fields before base 7 8 (2*level+1) (2*level+1) data.cursorValue data.width
      refine ⟨after,?_,ZeroData.sameMemory P base level clock (2*level+1) read write previous before after data rfl rfl fields.2.2.1,
        rfl,⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,fields.2.2.1⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_add] using run
    | succ remaining ih =>
      intro cursor before remainingEq cursorBound data position
      have inside : cursor<2*level+1 := by omega
      let next := zeroIteration origin before base level write cursor
      have iteration := zeroIteration_correct input P origin base level clock cursor read write previous before data position inside levelBound
      obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
        ih (cursor+1) next (by omega) (by omega) iteration.2.1 iteration.2.2
      have combined := iteration.1.trans run
      have cost : 375+(375*(2*level+1-(cursor+1))+135)=375*(2*level+1-cursor)+135 := by omega
      have firstFrame := zeroIteration_frame input P origin base level clock cursor read write previous before data inside levelBound
      have preserved := zeroIteration_preserved origin base level write cursor before data.cursorValue data.width
      exact ⟨after,cost ▸ combined,done,last,firstFrame.trans frame,
        output.trans preserved.1,fresh.trans preserved.2⟩
  exact go (2*level+1-cursor) cursor before rfl cursorBound data position

/-- Genuine whole zero loop. Only its actually visited prefix was
initialized at any earlier iteration; no destination suffix or incoming
destination row is supplied as an oracle. -/
theorem zero_complete (input : List Cell) (P : Parameters)
    (origin base level clock read write : ℕ) (previous : Array ℚ) (before : State)
    (header : Header P base level before) (buffers : Buffers base P.certificate.M read write)
    (position : before.pc=labelAddress origin .zeroGate)
    (clockValue : before.heap (base+6)=.natural clock)
    (cursorValue : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1))
    (readValue : before.heap (base+9)=.natural read) (writeValue : before.heap (base+10)=.natural write)
    (previousSize : previous.size=2*level+1) (readRow : RowAt before read previous)
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (1000*(level+1)) ∧
      ZeroData P base level clock (2*level+1) read write previous after ∧
      after.pc=labelAddress origin .scatterStart ∧ RowAt after write (Array.replicate (2*level+1) (0 : ℚ)) ∧
      MemoryFrame (region base P.certificate.M) before after ∧
      after.output=before.output ∧ after.register .fresh=before.register .fresh := by
  have initial : ZeroData P base level clock 0 read write previous before :=
    ⟨header,buffers,clockValue,cursorValue,width,readValue,writeValue,previousSize,readRow,
      RowPrefix.zero before write (Array.replicate (2*level+1) (0 : ℚ))⟩
  obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
    zeroLoop input P origin base level clock 0 read write previous before initial position (by omega) levelBound
  have complete : RowAt after write (Array.replicate (2*level+1) (0 : ℚ)) := by
    apply RowPrefix.complete after write (Array.replicate (2*level+1) (0 : ℚ))
    simpa only [Array.size_replicate] using done.zeroPrefix
  exact ⟨after,run.mono (by omega),done,last,complete,frame,output,fresh⟩

end PDROC.CalibrationRow
