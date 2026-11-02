module

public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Actual initialization-loop invariant. At cursor zero the RowPrefix
field is vacuous, so no old row contents are assumed initialized. -/
structure InitData (P : Parameters) (base level cursor : ℕ) (state : State) : Prop where
  header : Header P base level state
  cursorValue : state.heap (base+7)=.natural cursor
  width : state.heap (base+8)=.natural (2*level+1)
  read : state.heap (base+9)=.natural (firstRow base)
  write : state.heap (base+10)=.natural (secondRow base P.certificate.M)
  prefixRow : RowPrefix state (firstRow base) (P.walkRow level true 0) cursor

theorem InitData.sameMemory (P : Parameters) (base level cursor : ℕ) (before after : State)
    (data : InitData P base level cursor before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) : InitData P base level cursor after := by
  have header : Header P base level after :=
    Header.transport P base level before after data.header
      ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
      (by rw [live]) fresh
  refine ⟨header,?_,?_,?_,?_,?_⟩
  · rw [heap]; exact data.cursorValue
  · rw [heap]; exact data.width
  · rw [heap]; exact data.read
  · rw [heap]; exact data.write
  · exact ⟨data.prefixRow.bound,fun i inside => by rw [live]; exact data.prefixRow.live i inside,
      fun i inside => by rw [heap]; exact data.prefixRow.value i inside⟩

theorem InitData.advance (P : Parameters) (base level cursor : ℕ) (before : State)
    (data : InitData P base level cursor before) (inside : cursor<2*level+1)
    (levelBound : level≤P.certificate.M+1)
    (value : before.register .value=.rational (if cursor=level then 1 else 0)) :
    InitData P base level (cursor+1) (initStoreResult before base cursor) := by
  have widthBound : cursor<rowWidth P.certificate.M :=
    inside.trans_le (activeWidth_le P.certificate.M level levelBound)
  have fields := initStore_fields before base cursor
  have header_ne (offset : ℕ) (bound : offset<16) : base+offset≠firstRow base+cursor := by
    unfold firstRow
    omega
  refine ⟨initStore_header P before base level cursor data.header widthBound,?_,?_,?_,?_,
    initStore_delta_prefix P before base level cursor inside data.prefixRow value⟩
  · rw [fields.1]
    simp
  · rw [fields.1,Function.update_of_ne (by omega : base+8≠base+7),
      Function.update_of_ne (header_ne 8 (by decide))]
    exact data.width
  · rw [fields.1,Function.update_of_ne (by omega : base+9≠base+7),
      Function.update_of_ne (header_ne 9 (by decide))]
    exact data.read
  · rw [fields.1,Function.update_of_ne (by omega : base+10≠base+7),
      Function.update_of_ne (header_ne 10 (by decide))]
    exact data.write

theorem InitData.advance_control (P : Parameters) (origin base level cursor : ℕ) (before : State)
    (data : InitData P base level cursor before) (inside : cursor<2*level+1)
    (levelBound : level≤P.certificate.M+1)
    (value : before.register .value=.rational (if cursor=level then 1 else 0)) :
    InitData P base level (cursor+1) (initStoreNext origin before base cursor) := by
  have stored := InitData.advance P base level cursor before data inside levelBound value
  exact InitData.sameMemory P base level (cursor+1) (initStoreResult before base cursor)
    (initStoreNext origin before base cursor) stored rfl rfl rfl

theorem InitData.complete (P : Parameters) (base level : ℕ) (state : State)
    (data : InitData P base level (2*level+1) state) :
    RowAt state (firstRow base) (P.walkRow level true 0) := by
  apply RowPrefix.complete state (firstRow base) (P.walkRow level true 0)
  simpa only [PDROC.endpointWalkRow_size] using data.prefixRow

end PDROC.CalibrationRow
