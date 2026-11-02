module

public import Paid.PDROC_CalibrationRow_Zero_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ZeroRuntime

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

structure Boundary (P : Parameters) (base level clock cursor read write : ℕ) (previous : Array ℚ)
    (caller state : State) : Prop where
  data : ZeroData P base level clock cursor read write previous state
  suffixHeap : ∀ (i : ℕ), cursor ≤ i → i < 2*level+1 → state.heap (write+i)=caller.heap (write+i)
  suffixLive : ∀ (i : ℕ), cursor ≤ i → i < 2*level+1 → (write+i∈state.live ↔ write+i∈caller.live)

theorem Boundary.sameMemory (P : Parameters) (base level clock cursor read write : ℕ) (previous : Array ℚ)
    (caller before state : State) (entry : Boundary P base level clock cursor read write previous caller before)
    (heap : state.heap=before.heap) (live : state.live=before.live)
    (fresh : state.register .fresh=before.register .fresh) :
    Boundary P base level clock cursor read write previous caller state := by
  refine ⟨ZeroData.sameMemory P base level clock cursor read write previous before state entry.data heap live fresh,?_,?_⟩
  · intro i bound inside
    exact (congrFun heap _).trans (entry.suffixHeap i bound inside)
  · intro i bound inside
    rw [live]
    exact entry.suffixLive i bound inside

theorem Phase.sameMemory (P : Parameters) (base level clock read write : ℕ) (previous : Array ℚ)
    (written actualCursor : ℕ) (caller before state : State)
    (phase : Phase P base level clock read write previous written actualCursor caller before)
    (heap : state.heap=before.heap) (live : state.live=before.live)
    (fresh : state.register .fresh=before.register .fresh) :
    Phase P base level clock read write previous written actualCursor caller state := by
  have header := Header.transport P base level before state phase.header
    ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩ (by rw [live]) fresh
  refine ⟨header,phase.buffers,?_,?_,?_,?_,?_,phase.previousSize,?_,?_,?_,?_⟩
  · rw [heap]; exact phase.clockValue
  · rw [heap]; exact phase.cursorValue
  · rw [heap]; exact phase.width
  · rw [heap]; exact phase.readValue
  · rw [heap]; exact phase.writeValue
  · exact ⟨fun i inside => by rw [live]; exact phase.readRow.live i inside,
      fun i inside => by rw [heap]; exact phase.readRow.value i inside⟩
  · exact ⟨phase.zeroPrefix.bound,fun i inside => by rw [live]; exact phase.zeroPrefix.live i inside,
      fun i inside => by rw [heap]; exact phase.zeroPrefix.value i inside⟩
  · intro i bound inside
    exact (congrFun heap _).trans (phase.suffixHeap i bound inside)
  · intro i bound inside
    rw [live]
    exact phase.suffixLive i bound inside

theorem Boundary.rootPhase (P : Parameters) (base level clock cursor read write : ℕ) (previous : Array ℚ)
    (written actualCursor : ℕ) (caller before state : State)
    (entry : Boundary P base level clock cursor read write previous caller before)
    (phase : Phase P base level clock read write previous written actualCursor before state)
    (advanced : cursor ≤ written) :
    Phase P base level clock read write previous written actualCursor caller state := by
  refine ⟨phase.header,phase.buffers,phase.clockValue,phase.cursorValue,phase.width,phase.readValue,phase.writeValue,
    phase.previousSize,phase.readRow,phase.zeroPrefix,?_,?_⟩
  · intro i bound inside
    exact (phase.suffixHeap i bound inside).trans (entry.suffixHeap i (advanced.trans bound) inside)
  · intro i bound inside
    exact (phase.suffixLive i bound inside).trans (entry.suffixLive i (advanced.trans bound) inside)

theorem Boundary.advance (input : List Cell) (P : Parameters) (base level clock cursor read write : ℕ)
    (previous : Array ℚ) (caller before : State)
    (entry : Boundary P base level clock cursor read write previous caller before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural cursor) :
    Boundary P base level clock (cursor+1) read write previous caller (zeroCellResult before base write cursor) := by
  have fields := zeroCell_fields before base write cursor
  have phase := phase_afterCursorWrite input P base level clock cursor read write previous before
    (zeroCellResult before base write cursor) entry.data inside levelBound index fields.1 fields.2.1 fields.2.2.1
  refine ⟨ZeroData.advance input P base level clock cursor read write previous before entry.data inside levelBound index,?_,?_⟩
  · intro i bound inside
    exact (phase.suffixHeap i bound inside).trans (entry.suffixHeap i (by omega) inside)
  · intro i bound inside
    exact (phase.suffixLive i bound inside).trans (entry.suffixLive i (by omega) inside)

def Entry (P : Parameters) (base level clock cursor read write : ℕ) (previous : Array ℚ)
    (caller before : State) (label : Label) : Prop :=
  Boundary P base level clock cursor read write previous caller before ∧ cursor≤2*level+1 ∧
    (label=.zeroGate ∨ (label=.zeroCell ∧ cursor<2*level+1 ∧ before.register .index=.natural cursor))

def Closed (P : Parameters) (origin base level clock read write : ℕ) (previous : Array ℚ)
    (input : List Cell) (caller : State) (Good : State→Prop) : Prop :=
  ∀ cursor label before middle after,Entry P base level clock cursor read write previous caller before label →
    Good before → before.pc=labelAddress origin label →
    linearExecute input (basicBlock label).body before=some middle →
    (controlInstruction origin (basicBlock label).control).execute input middle=some after →
    ∀ state,((∃ count≤(basicBlock label).body.length,
      linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) → Good state

/-- Reuses the generic actual body/control preservation pattern. Root's
Scatter004 uses the same frozen primitives for its own phase entries. -/
theorem block_safe (P : Parameters) (origin base level clock cursor read write : ℕ) (previous : Array ℚ)
    (input : List Cell) (caller : State) (Good : State→Prop)
    (closed : Closed P origin base level clock read write previous input caller Good)
    (label : Label) (row : rowLabel label=true) (before middle after : State)
    (entry : Entry P base level clock cursor read write previous caller before label) (good : Good before)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames (region base P.certificate.M) input (basicBlock label).body before) :
    SafeSegment origin base (region base P.certificate.M) input Good before after
      (15*((basicBlock label).body.length+2)) := by
  have controlFrame := execute_memoryFrame (region base P.certificate.M)
    (controlInstruction origin (basicBlock label).control) input middle after
    (by cases (basicBlock label).control <;> trivial) control
  have bodyOutput := linearExecute_noOutput input _ (rowBody_noOutput label row) before middle body
  have controlOutput := execute_output_eq_of_noOutput _ input middle after
    (control_noOutput origin (basicBlock label).control) control
  have bodyFresh := rowBody_prefix_fresh input label before middle (basicBlock label).body.length
    (by simpa only [List.take_length] using body)
  have controlFresh := execute_preserves_fresh _ (control_noFresh origin (basicBlock label).control)
    input middle after control
  have bodyLive := linearExecute_live_mono input _ (rowBody_noRelease label row) before middle body
  have controlLive := execute_live_mono _ input middle after
    (by cases (basicBlock label).control <;> rfl) control
  exact SafeSegment.ofBlock origin base _ input Good label row before middle after position body control frames
    entry.1.data.header.live ((frames.final body).trans controlFrame)
    (controlOutput.trans bodyOutput) (controlFresh.trans bodyFresh) (bodyLive.trans controlLive)
    (closed cursor label before middle after entry good position body control)

end PDROC.CalibrationRow.ZeroRuntime
