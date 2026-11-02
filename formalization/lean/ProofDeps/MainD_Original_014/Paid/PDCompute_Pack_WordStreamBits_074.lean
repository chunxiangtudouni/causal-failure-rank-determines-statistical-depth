module
public import Paid.PDCompute_Pack_DenseWriteBlockBits_073
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_Pack_WordStream_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (loadSlot loadSlotResult storeSlot storeSlotResult HeapList)

theorem wordStreamLocal_trace_safe (program : Program) (input : List Cell) (before : State)
    (base pointer pointerSlot source budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (pointerInside : pointerSlot<headerWords) (inside : source<headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : values pointerSlot=.natural pointer)
    (outside : pointer<base ∨ base+headerWords ≤ pointer)
    (safe : SafeBits before budget)
    (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+1) ≤ budget)
    (counter : natBits (before.pc+12) ≤ budget)
    (fetched : FetchesCode program before.pc (wordStreamCode pointerSlot source)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 240 ∧
      Header after base (Function.update values outputCursor (.natural (pointer+1))) ∧
      HeapList after pointer [values source] ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+12 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (localRegion base pointer 1)) ∧
      (∀ state∈trace,SafeBits state budget) := by
  unfold wordStreamCode at fetched
  simp only [List.append_assoc] at fetched
  have loadFetch:=fetched.append_left
  obtain ⟨loadTrace,loadHead,loadLast,loadChain,loadTime,loadMemory,loadBits⟩:=
    loadSlot_trace_safe program input before base pointerSlot budget .old values header pointerInside hbase safe (addressBits pointerSlot pointerInside)
      ((natBits_mono (by omega : before.pc+3 ≤ before.pc+12)).trans counter) loadFetch
  let loaded:=loadSlotResult before base pointerSlot .old
  have loadedHeader : Header loaded base values:=header
  have loadedBase : loaded.register .fresh=.natural base := by simp [loaded,loadSlotResult,hbase]
  have loadedPointer : loaded.register .old=.natural pointer :=
    (header.loadSlot_execute input pointerSlot .old pointerInside hbase).2.trans hpointer
  have loadedPC : loaded.pc=before.pc+3:=rfl
  have loadedSafe : SafeBits loaded budget:=loadBits loaded (List.mem_of_getLast? loadLast)
  have loadedOutput : loaded.output=before.output:=rfl
  have emitFetch : FetchesCode program loaded.pc (denseWriteBlockCode source [values source].length) := by
    exact fetched.append_right.append_left
  have contents : ∀ (offset : ℕ) (bound : offset<[values source].length),values (source+offset)=[values source][offset] := by
    intro offset bound
    have eq : offset=0:=(by change offset<1 at bound;omega)
    subst offset
    rfl
  obtain ⟨emitTrace,written,emitHead,emitLast,emitChain,emitTime,writtenHeader,heap,writtenBase,writtenPointer,writtenPC,writtenOutput,emitMemory,emitBits⟩:=
    denseWriteBlock_trace_safe program input [values source] loaded base source pointer budget values loadedHeader
      (by simpa only [List.length_singleton] using Nat.succ_le_of_lt inside) loadedBase loadedPointer contents
      (by intro offset bound;have eq : offset=0:=(by change offset<1 at bound;omega);subst offset;exact outside) loadedSafe addressBits pointerBits
      ((natBits_mono (by rw [loadedPC];simp only [List.length_singleton];omega : loaded.pc+6*[values source].length ≤ before.pc+12)).trans counter) emitFetch
  have saveFetch : FetchesCode program written.pc (storeSlot outputCursor .old) := by
    rw [writtenPC]
    exact fetched.append_right.append_right
  have writtenSafe : SafeBits written budget:=emitBits written (List.mem_of_getLast? emitLast)
  have saveCounter : natBits (written.pc+3) ≤ budget:=by
    rw [writtenPC,loadedPC]
    simpa only [List.length_singleton,Nat.add_assoc] using counter
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory,saveBits⟩:=
    storeSlot_trace_safe program input written base outputCursor budget .old values writtenHeader (by decide) writtenBase (by decide)
      writtenSafe (addressBits outputCursor (by decide)) saveCounter saveFetch
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
      (RegionMemory.join_trace loadTrace emitTrace before loaded _ loadLast loadedRegion writtenRegion) savedRegion,
    joinTrace_invariant (joinTrace loadTrace emitTrace) saveTrace (fun state=>SafeBits state budget)
      (joinTrace_invariant loadTrace emitTrace (fun state=>SafeBits state budget) loadBits emitBits) saveBits⟩


end PDCompute.Pack
