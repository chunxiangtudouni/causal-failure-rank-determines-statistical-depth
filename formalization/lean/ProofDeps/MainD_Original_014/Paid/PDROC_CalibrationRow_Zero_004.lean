module

public import Paid.PDROC_CalibrationRow_Zero_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.ZeroRuntime

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem iteration_safe (input : List Cell) (P : Parameters) (origin base level clock cursor read write : ℕ)
    (previous : Array ℚ) (caller before : State) (Good : State→Prop)
    (closed : Closed P origin base level clock read write previous input caller Good)
    (entry : Boundary P base level clock cursor read write previous caller before) (good : Good before)
    (position : before.pc=labelAddress origin .zeroGate)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      (zeroIteration origin before base level write cursor) 375 ∧
      Boundary P base level clock (cursor+1) read write previous caller (zeroIteration origin before base level write cursor) ∧
      (zeroIteration origin before base level write cursor).pc=labelAddress origin .zeroGate := by
  let gate := gateResult before base 7 8 cursor (2*level+1)
  let entered : State := {gate with pc:=labelAddress origin .zeroCell}
  have fields := gate_fields before base 7 8 cursor (2*level+1) entry.data.cursorValue entry.data.width
  have gateBody : linearExecute input (basicBlock .zeroGate).body before=some gate := by
    rw [zeroGate_body]
    exact gate_execute input before base 7 8 cursor (2*level+1) entry.data.header.fresh
      (entry.data.header.live 7 (by decide)) (entry.data.header.live 8 (by decide)) entry.data.cursorValue entry.data.width
  have gateControl : (controlInstruction origin (basicBlock .zeroGate).control).execute input gate=some entered := by
    simpa only [basicBlock,inside,ite_true,gate,entered] using
      gate_control_execute input before base 7 8 cursor (2*level+1) origin .scatterStart .zeroCell
  have gateRun : SafeSegment origin base (region base P.certificate.M) input Good before entered 135 :=
    block_safe P origin base level clock cursor read write previous input caller Good closed .zeroGate rfl
      before gate entered ⟨entry,inside.le,Or.inl rfl⟩ good position gateBody gateControl
      (by simpa only [zeroGate_body] using gate_prefix_frames (region base P.certificate.M) input before 7 8)
  have enteredEntry := Boundary.sameMemory P base level clock cursor read write previous caller before entered entry rfl rfl fields.2.2.1
  have index : entered.register .index=.natural cursor := fields.2.2.2.1
  have cellBody := zeroCell_execute input P entered base level read write cursor enteredEntry.data.header enteredEntry.data.buffers
    enteredEntry.data.writeValue enteredEntry.data.cursorValue index
  have cellControl : (controlInstruction origin (basicBlock .zeroCell).control).execute input
      (zeroCellResult entered base write cursor)=some (zeroIteration origin before base level write cursor) := rfl
  have cellRun : SafeSegment origin base (region base P.certificate.M) input Good entered
      (zeroIteration origin before base level write cursor) 240 :=
    block_safe P origin base level clock cursor read write previous input caller Good closed .zeroCell rfl
      entered (zeroCellResult entered base write cursor) (zeroIteration origin before base level write cursor)
      ⟨enteredEntry,inside.le,Or.inr ⟨rfl,inside,index⟩⟩ gateRun.final.2.2.2.2 rfl cellBody cellControl
      (zeroCell_prefix_frames input P entered base level read write cursor enteredEntry.data.header enteredEntry.data.buffers
        enteredEntry.data.writeValue enteredEntry.data.cursorValue index (inside.trans_le (activeWidth_le _ _ levelBound)))
  have done := Boundary.advance input P base level clock cursor read write previous caller entered enteredEntry inside levelBound index
  exact ⟨gateRun.trans cellRun,
    Boundary.sameMemory P base level clock (cursor+1) read write previous caller
      (zeroCellResult entered base write cursor) (zeroIteration origin before base level write cursor) done rfl rfl rfl,rfl⟩

theorem loop_safe (input : List Cell) (P : Parameters) (origin base level clock cursor read write : ℕ)
    (previous : Array ℚ) (caller before : State) (Good : State→Prop)
    (closed : Closed P origin base level clock read write previous input caller Good)
    (entry : Boundary P base level clock cursor read write previous caller before) (good : Good before)
    (position : before.pc=labelAddress origin .zeroGate)
    (cursorBound : cursor≤2*level+1) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after
      (375*(2*level+1-cursor)+135) ∧ Boundary P base level clock (2*level+1) read write previous caller after ∧
      after.pc=labelAddress origin .scatterStart := by
  have go (remaining : ℕ) : ∀ cursor before,2*level+1-cursor=remaining → cursor≤2*level+1 →
      Boundary P base level clock cursor read write previous caller before → Good before →
      before.pc=labelAddress origin .zeroGate →
      ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after
        (375*(2*level+1-cursor)+135) ∧ Boundary P base level clock (2*level+1) read write previous caller after ∧
        after.pc=labelAddress origin .scatterStart := by
    induction remaining with
    | zero =>
      intro cursor before remainingEq cursorBound entry good position
      have equal : cursor=2*level+1 := by omega
      subst cursor
      let middle := gateResult before base 7 8 (2*level+1) (2*level+1)
      let after : State := {middle with pc:=labelAddress origin .scatterStart}
      have body : linearExecute input (basicBlock .zeroGate).body before=some middle := by
        rw [zeroGate_body]
        exact gate_execute input before base 7 8 (2*level+1) (2*level+1) entry.data.header.fresh
          (entry.data.header.live 7 (by decide)) (entry.data.header.live 8 (by decide)) entry.data.cursorValue entry.data.width
      have control : (controlInstruction origin (basicBlock .zeroGate).control).execute input middle=some after := by
        simpa only [basicBlock,lt_self_iff_false,ite_false,middle,after] using
          gate_control_execute input before base 7 8 (2*level+1) (2*level+1) origin .scatterStart .zeroCell
      have fields := gate_fields before base 7 8 (2*level+1) (2*level+1) entry.data.cursorValue entry.data.width
      have run : SafeSegment origin base (region base P.certificate.M) input Good before after 135 :=
        block_safe P origin base level clock (2*level+1) read write previous input caller Good closed .zeroGate rfl
          before middle after ⟨entry,Nat.le_refl _,Or.inl rfl⟩ good position body control
          (by simpa only [zeroGate_body] using gate_prefix_frames (region base P.certificate.M) input before 7 8)
      refine ⟨after,?_,Boundary.sameMemory P base level clock (2*level+1) read write previous caller
        before after entry rfl rfl fields.2.2.1,rfl⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_add] using run
    | succ remaining ih =>
      intro cursor before remainingEq cursorBound entry good position
      have inside : cursor<2*level+1 := by omega
      let next := zeroIteration origin before base level write cursor
      have iteration := iteration_safe input P origin base level clock cursor read write previous caller before Good closed
        entry good position inside levelBound
      obtain ⟨after,run,done,last⟩ := ih (cursor+1) next (by omega) (by omega) iteration.2.1 iteration.1.final.2.2.2.2 iteration.2.2
      have cost : 375+(375*(2*level+1-(cursor+1))+135)=375*(2*level+1-cursor)+135 := by omega
      exact ⟨after,cost ▸ iteration.1.trans run,done,last⟩
  exact go (2*level+1-cursor) cursor before rfl cursorBound entry good position

theorem complete_safe (input : List Cell) (P : Parameters) (origin base level clock read write : ℕ)
    (previous : Array ℚ) (before : State) (Good : State→Prop)
    (closed : Closed P origin base level clock read write previous input before Good)
    (header : Header P base level before) (buffers : Buffers base P.certificate.M read write) (good : Good before)
    (position : before.pc=labelAddress origin .zeroGate)
    (clockValue : before.heap (base+6)=.natural clock) (cursorValue : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1)) (readValue : before.heap (base+9)=.natural read)
    (writeValue : before.heap (base+10)=.natural write) (previousSize : previous.size=2*level+1)
    (readRow : RowAt before read previous) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after (1000*(level+1)) ∧
      ZeroData P base level clock (2*level+1) read write previous after ∧ after.pc=labelAddress origin .scatterStart ∧
      RowAt after write (Array.replicate (2*level+1) (0 : ℚ)) := by
  have initialData : ZeroData P base level clock 0 read write previous before :=
    ⟨header,buffers,clockValue,cursorValue,width,readValue,writeValue,previousSize,readRow,
      RowPrefix.zero before write (Array.replicate (2*level+1) (0 : ℚ))⟩
  have initial : Boundary P base level clock 0 read write previous before before :=
    ⟨initialData,fun _ _ _ => rfl,fun _ _ _ => Iff.rfl⟩
  obtain ⟨after,run,done,last⟩ := loop_safe input P origin base level clock 0 read write previous before before Good closed
    initial good position (by omega) levelBound
  have complete : RowAt after write (Array.replicate (2*level+1) (0 : ℚ)) := by
    apply RowPrefix.complete after write (Array.replicate (2*level+1) (0 : ℚ))
    simpa only [Array.size_replicate] using done.data.zeroPrefix
  exact ⟨after,run.mono (by omega),done.data,last,complete⟩

end PDROC.CalibrationRow.ZeroRuntime
