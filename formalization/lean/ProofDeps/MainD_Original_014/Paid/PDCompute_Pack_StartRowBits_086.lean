module
public import Paid.PDCompute_Pack_WordStreamBits_074
public import Paid.PDCompute_Pack_CopyBits_085
public import Paid.PDCompute_Pack_StartRow_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem startRowLocal_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer budget : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+67)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : values outputCursor=.natural pointer)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+1) ≤ budget) (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 345 ∧
      Header after base (startRowValues values pointer) ∧
      HeapList after pointer [values columnsPerRow] ∧ after.register .fresh=.natural base ∧
      after.pc=origin+85 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (localRegion base pointer 1)) ∧ (∀ state∈trace,SafeBits state budget) := by
  have fetched : FetchesCode program before.pc
      (wordStreamCode outputCursor columnsPerRow++copySlot columnsPerRow columnRemaining) := by
    rw [pc,←startRow_decompose]
    exact fetch_startRow program origin code
  obtain ⟨wordTrace,written,wordHead,wordLast,wordChain,wordTime,writtenHeader,wordHeap,writtenBase,writtenPC,writtenOutput,wordMemory,wordBits⟩:=
    wordStreamLocal_trace_safe program input before base pointer outputCursor columnsPerRow budget values header
      (by decide) (by decide) hbase hpointer outside safe addressBits pointerBits (pcBits _ (by omega)) fetched.append_left
  have copyFetch : FetchesCode program written.pc (copySlot columnsPerRow columnRemaining) := by
    rw [writtenPC]
    exact fetched.append_right
  have writtenSafe : SafeBits written budget:=wordBits written (List.mem_of_getLast? wordLast)
  obtain ⟨copyTrace,copyHead,copyLast,copyChain,copyTime,afterHeader,afterBase,afterPC,afterOutput,copyMemory,copyBits⟩:=
    copy_trace_safe program input written base columnsPerRow columnRemaining budget _ writtenHeader (by decide) (by decide) writtenBase
      writtenSafe (addressBits columnsPerRow (by decide)) (addressBits columnRemaining (by decide))
      (pcBits _ (by rw [writtenPC];omega)) copyFetch
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
    RegionMemory.join_trace wordTrace copyTrace before written _ wordLast wordMemory copyRegion,joinTrace_invariant wordTrace copyTrace (fun state=>SafeBits state budget) wordBits copyBits⟩


end PDCompute.Pack
