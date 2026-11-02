module

public import Paid.PDROC_CalibrationRow_Zero_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.ZeroRuntime

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Written prefix and the ACTUAL header7 cursor are separate fields.
The destination suffix is preserved as the caller's exact old heap/live,
with no zero-value, initialization or bit-size assumption on that suffix. -/
structure Phase (P : Parameters) (base level clock read write : ℕ) (previous : Array ℚ)
    (written actualCursor : ℕ) (before state : State) : Prop where
  header : Header P base level state
  buffers : Buffers base P.certificate.M read write
  clockValue : state.heap (base+6)=.natural clock
  cursorValue : state.heap (base+7)=.natural actualCursor
  width : state.heap (base+8)=.natural (2*level+1)
  readValue : state.heap (base+9)=.natural read
  writeValue : state.heap (base+10)=.natural write
  previousSize : previous.size=2*level+1
  readRow : RowAt state read previous
  zeroPrefix : RowPrefix state write (Array.replicate (2*level+1) (0 : ℚ)) written
  suffixHeap : ∀ (i : ℕ), written ≤ i → i < 2*level+1 → state.heap (write+i)=before.heap (write+i)
  suffixLive : ∀ (i : ℕ), written ≤ i → i < 2*level+1 → (write+i∈state.live ↔ write+i∈before.live)

theorem read_header_ne (base M read write index offset : ℕ) (buffers : Buffers base M read write)
    (bound : offset<16) : read+index≠base+offset := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> omega

theorem phase_sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (previous : Array ℚ) (before state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (heap : state.heap=before.heap) (live : state.live=before.live)
    (fresh : state.register .fresh=before.register .fresh) :
    Phase P base level clock read write previous cursor cursor before state := by
  have same := ZeroData.sameMemory P base level clock cursor read write previous before state data heap live fresh
  refine ⟨same.header,same.buffers,same.clockValue,same.cursorValue,same.width,same.readValue,same.writeValue,
    same.previousSize,same.readRow,same.zeroPrefix,?_,?_⟩
  · intro i _ _
    exact congrFun heap _
  · intro i _ _
    rw [live]

/-- A genuine state after the first six instructions and before the
last cursor store: row prefix cursor+1, actual header7 still cursor. -/
theorem phase_afterRowWrite (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (previous : Array ℚ) (before state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural cursor)
    (heap : state.heap=Function.update before.heap (write+cursor) (.rational 0))
    (live : state.live=insert (write+cursor) before.live)
    (fresh : state.register .fresh=before.register .fresh) :
    Phase P base level clock read write previous (cursor+1) cursor before state := by
  have done := ZeroData.advance input P base level clock cursor read write previous before data inside levelBound index
  have fields := zeroCell_fields before base write cursor
  have fullLive : (zeroCellResult before base write cursor).live=state.live := by
    rw [fields.2.1,live]
    exact Finset.insert_eq_of_mem (Finset.mem_insert_of_mem (data.header.live 7 (by decide)))
  have lookup (offset : ℕ) (bound : offset<16) : state.heap (base+offset)=before.heap (base+offset) := by
    rw [heap,Function.update_of_ne (Ne.symm (Buffers.write_header_ne base P.certificate.M read write cursor offset data.buffers bound))]
  have frame : MemoryFrame (region base P.certificate.M) before state :=
    frame_of_one_update _ before state (write+cursor) (.rational 0)
      (Buffers.write_mem base P.certificate.M read write cursor data.buffers
        (inside.trans_le (activeWidth_le _ _ levelBound))) heap live
  have header := Header.transport P base level before state data.header frame
    (by rw [live]; exact Finset.subset_insert _ _) fresh
  have readRow : RowAt state read previous := by
    constructor
    · intro i bound
      rw [←fullLive]
      exact done.readRow.live i bound
    · intro i bound
      have value := done.readRow.value i bound
      rw [fields.1,Function.update_of_ne (read_header_ne base P.certificate.M read write i 7 data.buffers (by decide))] at value
      rw [heap]
      exact value
  have zeroPrefix : RowPrefix state write (Array.replicate (2*level+1) (0 : ℚ)) (cursor+1) := by
    apply RowPrefix.transport (zeroCellResult before base write cursor) state write
      (Array.replicate (2*level+1) (0 : ℚ)) (cursor+1) done.zeroPrefix
    · rw [fullLive]
    · intro i _
      rw [heap,fields.1,Function.update_of_ne (Buffers.write_header_ne base P.certificate.M read write i 7 data.buffers (by decide))]
  refine ⟨header,data.buffers,(lookup 6 (by decide)).trans data.clockValue,
    (lookup 7 (by decide)).trans data.cursorValue,(lookup 8 (by decide)).trans data.width,
    (lookup 9 (by decide)).trans data.readValue,(lookup 10 (by decide)).trans data.writeValue,
    data.previousSize,readRow,zeroPrefix,?_,?_⟩
  · intro i afterWritten _
    have different : write+i≠write+cursor := by omega
    rw [heap,Function.update_of_ne different]
  · intro i afterWritten _
    have different : write+i≠write+cursor := by omega
    rw [live]
    simp only [Finset.mem_insert,different,false_or]

theorem phase_afterCursorWrite (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (previous : Array ℚ) (before state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural cursor)
    (heap : state.heap=Function.update (Function.update before.heap (write+cursor) (.rational 0))
      (base+7) (.natural (cursor+1)))
    (live : state.live=insert (base+7) (insert (write+cursor) before.live))
    (fresh : state.register .fresh=before.register .fresh) :
    Phase P base level clock read write previous (cursor+1) (cursor+1) before state := by
  have done := ZeroData.advance input P base level clock cursor read write previous before data inside levelBound index
  have fields := zeroCell_fields before base write cursor
  have same := ZeroData.sameMemory P base level clock (cursor+1) read write previous
    (zeroCellResult before base write cursor) state done (heap.trans fields.1.symm)
    (live.trans fields.2.1.symm) (fresh.trans fields.2.2.1.symm)
  refine ⟨same.header,same.buffers,same.clockValue,same.cursorValue,same.width,same.readValue,same.writeValue,
    same.previousSize,same.readRow,same.zeroPrefix,?_,?_⟩
  · intro i afterWritten _
    have different : write+i≠write+cursor := by omega
    rw [heap,Function.update_of_ne (Buffers.write_header_ne base P.certificate.M read write i 7 data.buffers (by decide)),
      Function.update_of_ne different]
  · intro i afterWritten _
    have different : write+i≠write+cursor := by omega
    rw [live]
    simp only [Finset.mem_insert,Buffers.write_header_ne base P.certificate.M read write i 7 data.buffers (by decide),
      different,false_or]

def prefixWritten (cursor count : ℕ) : ℕ := if count<6 then cursor else cursor+1
def prefixCursor (cursor count : ℕ) : ℕ := if count<14 then cursor else cursor+1

theorem zeroCell_prefix_phase (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (previous : Array ℚ) (before state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural cursor) (count : ℕ) (bound : count≤14)
    (run : linearExecute input ((basicBlock .zeroCell).body.take count) before=some state) :
    Phase P base level clock read write previous (prefixWritten cursor count) (prefixCursor cursor count) before state := by
  have fields := zeroCell_heap_live_prefix input P base level clock cursor read write previous before state data index count bound run
  have fresh := rowBody_prefix_fresh input .zeroCell before state count run
  by_cases early : count<6
  · have beforeEnd : count<14 := by omega
    have heap : state.heap=before.heap := by simpa only [early,ite_true] using fields.1
    have live : state.live=before.live := by simpa only [early,ite_true] using fields.2
    simpa only [prefixWritten,prefixCursor,early,beforeEnd,ite_true] using
      phase_sameMemory P base level clock cursor read write previous before state data heap live fresh
  · by_cases middle : count<14
    · have heap : state.heap=Function.update before.heap (write+cursor) (.rational 0) := by
        simpa only [early,ite_false,middle,ite_true] using fields.1
      have live : state.live=insert (write+cursor) before.live := by
        simpa only [early,ite_false,middle,ite_true] using fields.2
      simpa only [prefixWritten,prefixCursor,early,ite_false,middle,ite_true] using
        phase_afterRowWrite input P base level clock cursor read write previous before state data inside levelBound index heap live fresh
    · have heap : state.heap=Function.update (Function.update before.heap (write+cursor) (.rational 0))
          (base+7) (.natural (cursor+1)) := by simpa only [early,middle,ite_false] using fields.1
      have live : state.live=insert (base+7) (insert (write+cursor) before.live) := by
        simpa only [early,middle,ite_false] using fields.2
      simpa only [prefixWritten,prefixCursor,early,middle,ite_false] using
        phase_afterCursorWrite input P base level clock cursor read write previous before state data inside levelBound index heap live fresh

end PDROC.CalibrationRow.ZeroRuntime
