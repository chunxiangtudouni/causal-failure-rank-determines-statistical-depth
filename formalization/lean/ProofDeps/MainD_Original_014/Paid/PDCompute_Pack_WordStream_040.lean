module
public import Paid.PDCompute_Pack_LocalRegion_044
public import Paid.PDCompute_Pack_PointerMemory_017
public import Paid.PDCompute_SolverSmallTraceMemory_061
public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (loadSlot loadSlotResult storeSlot storeSlotResult HeapList)

def wordStreamCode (pointerSlot source : ℕ) : List Instruction :=
  loadSlot pointerSlot .old++denseWriteBlockCode source 1++storeSlot outputCursor .old

theorem wordStreamCode_length (pointerSlot source : ℕ) : (wordStreamCode pointerSlot source).length=12 := rfl

theorem _root_.PDLower.CalibrationCompute.HeapList.headerMemory {before after : State} {pointer base : ℕ} {cells : List Cell}
    (heap : HeapList before pointer cells) (memory : HeaderMemory before after base)
    (outside : ∀ offset<cells.length,pointer+offset<base ∨ base+headerWords ≤ pointer+offset) :
    HeapList after pointer cells := by
  apply HeapList.of_values
  · intro offset bound
    rw [memory.2.1]
    exact heap.1 offset bound
  · intro offset bound
    rw [memory.1 (pointer+offset) (outside offset bound)]
    exact heap.value offset bound

/-- Actual streaming of the original table/row length word, followed
by saving the incremented cursor. Preexisting result live cells allowed. -/
theorem wordStreamLocal_trace (program : Program) (input : List Cell) (before : State)
    (base pointer pointerSlot source : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (pointerInside : pointerSlot<headerWords) (inside : source<headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : values pointerSlot=.natural pointer)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    (fetched : FetchesCode program before.pc (wordStreamCode pointerSlot source)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 240 ∧
      Header after base (Function.update values outputCursor (.natural (pointer+1))) ∧
      HeapList after pointer [values source] ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+12 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer 1) := by
  unfold wordStreamCode at fetched
  simp only [List.append_assoc] at fetched
  have loadFetch:=fetched.append_left
  obtain ⟨loadTrace,loadHead,loadLast,loadChain,loadTime,loadMemory⟩:=
    header.loadSlot_trace_memory program input pointerSlot .old pointerInside hbase loadFetch
  let loaded:=loadSlotResult before base pointerSlot .old
  have loadedHeader : Header loaded base values:=header
  have loadedBase : loaded.register .fresh=.natural base := by simp [loaded,loadSlotResult,hbase]
  have loadedPointer : loaded.register .old=.natural pointer :=
    (header.loadSlot_execute input pointerSlot .old pointerInside hbase).2.trans hpointer
  have loadedPC : loaded.pc=before.pc+3:=rfl
  have loadedOutput : loaded.output=before.output:=rfl
  have emitFetch : FetchesCode program loaded.pc (denseWriteBlockCode source [values source].length) := by
    exact fetched.append_right.append_left
  have contents : ∀ (offset : ℕ) (bound : offset<[values source].length),values (source+offset)=[values source][offset] := by
    intro offset bound
    have eq : offset=0:=(by change offset<1 at bound;omega)
    subst offset
    rfl
  obtain ⟨emitTrace,written,emitHead,emitLast,emitChain,emitTime,writtenHeader,heap,writtenBase,writtenPointer,writtenPC,writtenOutput,emitMemory⟩:=
    denseWriteBlock_trace program input [values source] loaded base source pointer values loadedHeader
      (by simpa only [List.length_singleton] using Nat.succ_le_of_lt inside) loadedBase loadedPointer contents
      (by intro offset bound;have eq : offset=0:=(by change offset<1 at bound;omega);subst offset;exact outside) emitFetch
  have saveFetch : FetchesCode program written.pc (storeSlot outputCursor .old) := by
    rw [writtenPC]
    exact fetched.append_right.append_right
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory⟩:=
    writtenHeader.storeSlot_trace_memory program input outputCursor .old (by decide) writtenBase (by decide) saveFetch
  let after:=storeSlotResult written base outputCursor .old
  have afterHeader : Header after base (Function.update values outputCursor (.natural (pointer+1))) := by
    simpa only [List.length_singleton,writtenPointer] using header_store_result writtenHeader outputCursor .old
  have afterBase : after.register .fresh=.natural base := by simp [after,storeSlotResult,writtenBase]
  have afterPC : after.pc=before.pc+12 := by
    have savePC : after.pc=written.pc+3:=rfl
    simp only [List.length_singleton] at writtenPC
    omega
  have saveFinal:=HeaderMemory.trace_last saveMemory saveLast
  have afterHeap : HeapList after pointer [values source]:=heap.headerMemory saveFinal
    (by intro offset bound;have eq : offset=0:=(by change offset<1 at bound;omega);subst offset;exact outside)
  have loadedRegion : ∀ state∈loadTrace,RegionMemory before state (localRegion base pointer 1):=
    fun state member=>headerMemory_local base pointer 1 (loadMemory state member)
  have writtenRegion : ∀ state∈emitTrace,RegionMemory loaded state (localRegion base pointer 1):=
    fun state member=>emissionMemory_local base pointer 1 (emitMemory state member)
  have savedRegion : ∀ state∈saveTrace,RegionMemory written state (localRegion base pointer 1):=
    fun state member=>headerMemory_local base pointer 1 (saveMemory state member)
  have firstJoin:=joinTrace_spec program input loadTrace emitTrace before loaded written 60 120
    loadHead loadLast emitHead emitLast loadChain emitChain loadTime emitTime
  have lastJoin:=joinTrace_spec program input (joinTrace loadTrace emitTrace) saveTrace before written after 180 60
    firstJoin.1 firstJoin.2.1 saveHead saveLast firstJoin.2.2.1 saveChain firstJoin.2.2.2 saveTime
  exact ⟨joinTrace (joinTrace loadTrace emitTrace) saveTrace,after,lastJoin.1,lastJoin.2.1,lastJoin.2.2.1,lastJoin.2.2.2,
    afterHeader,afterHeap,afterBase,afterPC,saveFinal.2.2.trans (writtenOutput.trans loadedOutput),
    RegionMemory.join_trace (joinTrace loadTrace emitTrace) saveTrace before written _ firstJoin.2.1
      (RegionMemory.join_trace loadTrace emitTrace before loaded _ loadLast loadedRegion writtenRegion) savedRegion⟩

theorem wordStream_trace (program : Program) (input : List Cell) (before : State)
    (base pointer pointerSlot source n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (pointerInside : pointerSlot<headerWords) (inside : source<headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : values pointerSlot=.natural pointer)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    (lower : resultBase base n k ≤ pointer)
    (upper : pointer+1 ≤ resultBase base n k+resultCapacity n k)
    (fetched : FetchesCode program before.pc (wordStreamCode pointerSlot source)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 240 ∧
      Header after base (Function.update values outputCursor (.natural (pointer+1))) ∧
      HeapList after pointer [values source] ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+12 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (writeRegion base n k) := by
  obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPC,afterOutput,memory⟩:=
    wordStreamLocal_trace program input before base pointer pointerSlot source values header pointerInside inside
      hbase hpointer outside fetched
  exact ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPC,afterOutput,
    fun state member=>(memory state member).enlarge (localRegion_write_subset base n k pointer 1 lower upper)⟩

end PDCompute.Pack
