module

public import Paid.PDROC_CalibrationRow_Init_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem initIteration_safe (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (Good : State→Prop) (closed : InitClosed P origin base level input Good)
    (before : State) (data : InitData P base level cursor before) (good : Good before)
    (position : before.pc=labelAddress origin .initGate) (inside : cursor<2*level+1)
    (levelBound : level≤P.certificate.M+1) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      (initIteration origin before base level cursor) 600 ∧
      InitData P base level (cursor+1) (initIteration origin before base level cursor) ∧
      (initIteration origin before base level cursor).pc=labelAddress origin .initGate := by
  let pick := initPick origin before base level cursor
  have fields := initPick_fields origin before base level cursor data.cursorValue
  have picked : InitData P base level cursor pick :=
    InitData.sameMemory P base level cursor before pick data fields.1 fields.2.1 fields.2.2.1
  have pickRun := initPick_safe P origin base level cursor input Good closed before data good position inside
  have body := initStore_execute input pick base cursor picked.header.fresh
    (picked.header.live 9 (by decide)) picked.read (picked.header.live 7 (by decide))
    picked.cursorValue fields.2.2.2.1
  have widthInside := inside.trans_le (activeWidth_le P.certificate.M level levelBound)
  have storeFields := initStore_fields pick base cursor
  have storeRun : SafeSegment origin base (region base P.certificate.M) input Good pick
      (initStoreNext origin pick base cursor) 225 :=
    initBlock_safe P origin base level cursor input Good closed .initStore rfl pick
      (initStoreResult pick base cursor) (initStoreNext origin pick base cursor) picked inside.le
      (Or.inr ⟨inside,fields.2.2.2.1,Or.inr (Or.inr ⟨rfl,fields.2.2.2.2.1⟩)⟩)
      pickRun.final.2.2.2.2 fields.2.2.2.2.2.1 body
      (initStore_control_execute origin input pick base cursor)
      (initStore_prefix_frames input pick base P.certificate.M cursor picked.header.fresh
        (picked.header.live 9 (by decide)) picked.read (picked.header.live 7 (by decide))
        picked.cursorValue fields.2.2.2.1 widthInside)
      (initStore_frame pick base P.certificate.M cursor widthInside) storeFields.2.2.2.2.2 storeFields.2.2.1
      (by change pick.live ⊆ (initStoreResult pick base cursor).live
          rw [storeFields.2.1]
          exact fun _ member => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member))
  exact ⟨(pickRun.trans storeRun).mono (by decide : 300+225≤600),
    InitData.advance_control P origin base level cursor pick picked inside levelBound fields.2.2.2.2.1,rfl⟩

/-- The SAME complete initialization trace now preserves Good and every
state's frame/live/relative-register facts. Only actual block closure is
abstracted; all branching, stores and the finite loop are executed here. -/
theorem initLoop_safe (P : Parameters) (origin base level cursor : ℕ) (input : List Cell)
    (Good : State→Prop) (closed : InitClosed P origin base level input Good)
    (before : State) (data : InitData P base level cursor before) (good : Good before)
    (position : before.pc=labelAddress origin .initGate)
    (cursorBound : cursor≤2*level+1) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after
      (600*(2*level+1-cursor)+135) ∧ InitData P base level (2*level+1) after ∧
      after.pc=labelAddress origin .stepStart := by
  have go (remaining : ℕ) : ∀ cursor before,2*level+1-cursor=remaining →
      cursor≤2*level+1 → InitData P base level cursor before → Good before →
      before.pc=labelAddress origin .initGate →
      ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after
        (600*(2*level+1-cursor)+135) ∧ InitData P base level (2*level+1) after ∧
        after.pc=labelAddress origin .stepStart := by
    induction remaining with
    | zero =>
      intro cursor before remainingEq cursorBound data good position
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
      have fields := gate_fields before base 7 8 (2*level+1) (2*level+1) data.cursorValue data.width
      have run : SafeSegment origin base (region base P.certificate.M) input Good before after 135 :=
        initBlock_safe P origin base level (2*level+1) input Good closed .initGate rfl before middle after
          data (Nat.le_refl _) (Or.inl rfl) good position body control
          (by simpa only [initGate_body] using gate_prefix_frames (region base P.certificate.M) input before 7 8)
          ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ fields.2.2.2.2.2.2.2 fields.2.2.1 (fun _ member => member)
      refine ⟨after,?_,InitData.sameMemory P base level (2*level+1) before after data rfl rfl fields.2.2.1,rfl⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_add] using run
    | succ remaining ih =>
      intro cursor before remainingEq cursorBound data good position
      have inside : cursor<2*level+1 := by omega
      let next := initIteration origin before base level cursor
      have iteration := initIteration_safe P origin base level cursor input Good closed
        before data good position inside levelBound
      obtain ⟨after,run,done,last⟩ := ih (cursor+1) next (by omega) (by omega)
        iteration.2.1 iteration.1.final.2.2.2.2 iteration.2.2
      have cost : 600+(600*(2*level+1-(cursor+1))+135)=600*(2*level+1-cursor)+135 := by omega
      exact ⟨after,cost ▸ iteration.1.trans run,done,last⟩
  exact go (2*level+1-cursor) cursor before rfl cursorBound data good position

theorem init_complete_safe (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (Good : State→Prop) (closed : InitClosed P origin base level input Good)
    (before : State) (header : Header P base level before) (good : Good before)
    (position : before.pc=labelAddress origin .initGate)
    (cursor : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1))
    (read : before.heap (base+9)=.natural (firstRow base))
    (write : before.heap (base+10)=.natural (secondRow base P.certificate.M))
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after (1600*(level+1)) ∧
      after.pc=labelAddress origin .stepStart ∧ Header P base level after ∧
      after.heap (base+7)=.natural (2*level+1) ∧ after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (firstRow base) ∧
      after.heap (base+10)=.natural (secondRow base P.certificate.M) ∧
      RowAt after (firstRow base) (P.walkRow level true 0) := by
  have initial : InitData P base level 0 before :=
    ⟨header,cursor,width,read,write,RowPrefix.zero before (firstRow base) (P.walkRow level true 0)⟩
  obtain ⟨after,run,done,last⟩ := initLoop_safe P origin base level 0 input Good closed
    before initial good position (by omega) levelBound
  exact ⟨after,run.mono (by omega),last,done.header,done.cursorValue,done.width,done.read,done.write,
    InitData.complete P base level after done⟩

end PDROC.CalibrationRow
