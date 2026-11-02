module
public import Paid.PDCompute_Pack_WordStream_040
public import Paid.PDCompute_Pack_CopyTrace_039
public import Paid.PDCompute_Pack_Fragments_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem startRow_decompose : startRowCode=wordStreamCode outputCursor columnsPerRow++copySlot columnsPerRow columnRemaining := rfl

def startRowValues (values : ℕ → Cell) (pointer : ℕ) : ℕ → Cell :=
  Function.update (Function.update values outputCursor (.natural (pointer+1))) columnRemaining (values columnsPerRow)

/-- The actual row header is written and the actual column counter is
initialized before control reaches85. -/
theorem startRowLocal_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+67)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : values outputCursor=.natural pointer)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 345 ∧
      Header after base (startRowValues values pointer) ∧
      HeapList after pointer [values columnsPerRow] ∧ after.register .fresh=.natural base ∧
      after.pc=origin+85 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer 1) := by
  have fetched : FetchesCode program before.pc
      (wordStreamCode outputCursor columnsPerRow++copySlot columnsPerRow columnRemaining) := by
    rw [pc,←startRow_decompose]
    exact fetch_startRow program origin code
  obtain ⟨wordTrace,written,wordHead,wordLast,wordChain,wordTime,writtenHeader,wordHeap,writtenBase,writtenPC,writtenOutput,wordMemory⟩:=
    wordStreamLocal_trace program input before base pointer outputCursor columnsPerRow values header
      (by decide) (by decide) hbase hpointer outside fetched.append_left
  have copyFetch : FetchesCode program written.pc (copySlot columnsPerRow columnRemaining) := by
    rw [writtenPC]
    exact fetched.append_right
  obtain ⟨copyTrace,copyHead,copyLast,copyChain,copyTime,afterHeader,afterBase,afterPC,afterOutput,copyMemory⟩:=
    copy_trace program input written base columnsPerRow columnRemaining _ writtenHeader (by decide) (by decide) writtenBase copyFetch
  let after:=copySlotResult written base columnsPerRow columnRemaining
  have headerResult : Header after base (startRowValues values pointer) := by
    simpa only [startRowValues,Function.update_of_ne (by decide : columnsPerRow≠outputCursor)] using afterHeader
  have finalMemory:=HeaderMemory.trace_last copyMemory copyLast
  have heapResult : HeapList after pointer [values columnsPerRow]:=wordHeap.headerMemory finalMemory
    (by intro offset bound;have eq : offset=0:=(by change offset<1 at bound;omega);subst offset;exact outside)
  have copiedPC : after.pc=written.pc+6:=afterPC
  have finalPC : after.pc=origin+85 := by omega
  have copyRegion : ∀ state∈copyTrace,RegionMemory written state (localRegion base pointer 1):=
    fun state member=>headerMemory_local base pointer 1 (copyMemory state member)
  have joined:=joinTrace_spec program input wordTrace copyTrace before written after 240 105
    wordHead wordLast copyHead copyLast wordChain copyChain wordTime copyTime
  exact ⟨joinTrace wordTrace copyTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    headerResult,heapResult,afterBase,finalPC,afterOutput.trans writtenOutput,
    RegionMemory.join_trace wordTrace copyTrace before written _ wordLast wordMemory copyRegion⟩

theorem startRow_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer n k : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+67)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : values outputCursor=.natural pointer)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    (lower : resultBase base n k ≤ pointer)
    (upper : pointer+1 ≤ resultBase base n k+resultCapacity n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 345 ∧
      Header after base (startRowValues values pointer) ∧
      HeapList after pointer [values columnsPerRow] ∧ after.register .fresh=.natural base ∧
      after.pc=origin+85 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (writeRegion base n k) := by
  obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPC,afterOutput,memory⟩:=
    startRowLocal_trace program input origin before base pointer values code pc header hbase hpointer outside
  exact ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPC,afterOutput,
    fun state member=>(memory state member).enlarge (localRegion_write_subset base n k pointer 1 lower upper)⟩

end PDCompute.Pack
