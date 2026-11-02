module
public import Paid.PDCompute_Pack_DenseReadBlockBits_072
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_Pack_ReadDense_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

theorem readDense_trace_safe (program : Program) (input : List Cell) (before : State) (base pointer n k budget : ℕ)
    (entry : MenuEntry) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hpointer : values sourceCursor=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (safe : SafeBits before budget)
    (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+6) ≤ budget)
    (counter : natBits (before.pc+39) ≤ budget)
    (fetched : FetchesCode program before.pc readDenseCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤705 ∧
      Header after base (loadedEntryValues entry values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧
      after.pc=before.pc+39 ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  unfold readDenseCode at fetched
  let read:=loadSlotResult before base sourceCursor .old
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory,firstBits⟩:=
    loadSlot_trace_safe program input before base sourceCursor budget .old values header (by decide) hbase safe (addressBits sourceCursor (by decide))
      ((natBits_mono (by omega : before.pc+3 ≤ before.pc+39)).trans counter) fetched.append_left
  have readHeader : Header read base values := header.loadSlot_preserves sourceCursor .old
  have readBase : read.register .fresh=.natural base := (loadSlotResult_fresh before base sourceCursor .old (by decide)).trans hbase
  have readPointer : read.register .old=.natural pointer :=
    (header.loadSlot_execute input sourceCursor .old (by decide) hbase).2.trans hpointer
  have readSource : PDLower.CalibrationCompute.HeapList read pointer (denseEncodeEntry entry) := source
  have readPC : read.pc=before.pc+3 := rfl
  have readSafe : SafeBits read budget:=firstBits read (List.mem_of_getLast? firstLast)
  have tailCounter : natBits (read.pc+6*(denseEncodeEntry entry).length) ≤ budget:=by
    rw [readPC,denseEncodeEntry_length]
    simpa only [entryWords,Nat.add_assoc] using counter
  have tailPointerBits : 1+natBits (pointer+(denseEncodeEntry entry).length) ≤ budget:=by
    simpa only [denseEncodeEntry_length,entryWords] using pointerBits
  have tailFetch : FetchesCode program read.pc (denseReadBlockCode entryStart (denseEncodeEntry entry).length) := by
    rw [denseEncodeEntry_length]
    exact fetched.append_right
  have tailOutside : ∀ offset<(denseEncodeEntry entry).length,pointer+offset<base ∨ base+headerWords≤pointer+offset := by
    simpa only [denseEncodeEntry_length,entryWords] using outside
  obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterPC,_afterFrame,afterOutput,tailMemory,tailBits⟩:=
    denseReadBlock_trace_safe program input (denseEncodeEntry entry) read base entryStart pointer n k budget values readHeader
      (by rw [denseEncodeEntry_length];change 30≤48;decide) readBase readPointer readSource tailOutside readSafe addressBits tailPointerBits tailCounter tailFetch
  have tailBound : time program tail≤645 := by simpa only [denseEncodeEntry_length,entryWords] using tailTime
  have finalPointer : after.register .old=.natural (pointer+6) := by
    simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  have pc : after.pc=read.pc+36 := by simpa only [denseEncodeEntry_length,entryWords] using afterPC
  have joined:=joinTrace_spec program input firstTrace tail before read after 60 645
    firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailBound
  refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,finalPointer,?_,afterOutput,
    joinTrace_memory firstTrace tail before read base firstLast firstMemory tailMemory,
    joinTrace_invariant firstTrace tail (fun state=>SafeBits state budget) firstBits tailBits⟩
  omega


end PDCompute.Pack
