module

public import Paid.PDROC_CalibrationRow_023
public import Paid.PDLower_CalibrationCompute_IntermediateLeft_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Timed-phase controls, introduced only AFTER the actual stepStart
has stored natural zero into header6. Original Header stays weaker. -/
structure RowControl (P : Parameters) (base level clock cursor read write : ℕ) (state : State) : Prop where
  header : Header P base level state
  buffers : Buffers base P.certificate.M read write
  clockValue : state.heap (base+6)=.natural clock
  cursorValue : state.heap (base+7)=.natural cursor
  width : state.heap (base+8)=.natural (2*level+1)
  read : state.heap (base+9)=.natural read
  write : state.heap (base+10)=.natural write

theorem RowControl.sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (before after : State) (data : RowControl P base level clock cursor read write before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) :
    RowControl P base level clock cursor read write after := by
  have header := Header.transport P base level before after data.header
    ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
    (by intro a member; rw [live]; exact member) fresh
  refine ⟨header,data.buffers,?_,?_,?_,?_,?_⟩
  · rw [heap]; exact data.clockValue
  · rw [heap]; exact data.cursorValue
  · rw [heap]; exact data.width
  · rw [heap]; exact data.read
  · rw [heap]; exact data.write

structure ScatterData (P : Parameters) (base level clock cursor read write : ℕ) (state : State) : Prop where
  control : RowControl P base level clock cursor read write state
  readRow : RowAt state read (P.walkRow level true clock)
  writeRow : RowAt state write (rowScatterPrefix P level (P.walkRow level true clock) cursor)

/-- The first sequential bump is retained as its OWN physical phase,
even for the two letters of an absorbed source with equal targets. -/
structure ScatterLeftData (P : Parameters) (base level clock cursor read write : ℕ)
    (inside : cursor<2*level+1) (state : State) : Prop where
  control : RowControl P base level clock cursor read write state
  readRow : RowAt state read (P.walkRow level true clock)
  writeRow : RowAt state write (rowLeftPrefix P level clock cursor inside)

/-- After the right bump the array has prefix cursor+1, but the true
header7 still contains cursor until scatterNext really increments it. -/
structure ScatterBothData (P : Parameters) (base level clock cursor read write : ℕ) (state : State) : Prop where
  control : RowControl P base level clock cursor read write state
  readRow : RowAt state read (P.walkRow level true clock)
  writeRow : RowAt state write (rowScatterPrefix P level (P.walkRow level true clock) (cursor+1))

theorem ScatterData.sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (before after : State) (data : ScatterData P base level clock cursor read write before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) : ScatterData P base level clock cursor read write after := by
  have memory : MemoryFrame ∅ before after := ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
  exact ⟨RowControl.sameMemory P base level clock cursor read write before after data.control heap live fresh,
    empty_frame_row before after read _ data.readRow memory,empty_frame_row before after write _ data.writeRow memory⟩

theorem ScatterLeftData.sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (inside : cursor<2*level+1) (before after : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) : ScatterLeftData P base level clock cursor read write inside after := by
  have memory : MemoryFrame ∅ before after := ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
  exact ⟨RowControl.sameMemory P base level clock cursor read write before after data.control heap live fresh,
    empty_frame_row before after read _ data.readRow memory,empty_frame_row before after write _ data.writeRow memory⟩

theorem ScatterBothData.sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (before after : State) (data : ScatterBothData P base level clock cursor read write before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) : ScatterBothData P base level clock cursor read write after := by
  have memory : MemoryFrame ∅ before after := ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
  exact ⟨RowControl.sameMemory P base level clock cursor read write before after data.control heap live fresh,
    empty_frame_row before after read _ data.readRow memory,empty_frame_row before after write _ data.writeRow memory⟩

end PDROC.CalibrationRow
