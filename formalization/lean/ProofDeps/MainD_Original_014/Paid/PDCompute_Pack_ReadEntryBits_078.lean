module
public import Paid.PDCompute_Pack_ReadDenseBits_076
public import Paid.PDCompute_Pack_ReadTailBits_077
public import Paid.PDCompute_Pack_ReadEntry_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem readEntry_trace_safe (program : Program) (input : List Cell) (before : State) (base source pointer n k budget : ℕ)
    (entry : MenuEntry) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (dense : PDLower.CalibrationCompute.HeapList before source (denseEncodeEntry entry))
    (outside : ∀ offset<6,source+offset<base ∨ base+headerWords≤source+offset)
    (safe : SafeBits before budget)
    (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (sourceBits : 1+natBits (source+6) ≤ budget) (twoBits : 1+natBits 2 ≤ budget)
    (counter : natBits (before.pc+50) ≤ budget)
    (fetched : FetchesCode program before.pc readEntryCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤885 ∧
      Header after base (readTailValues (loadedEntryValues entry values) (source+6)) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural pointer ∧
      after.register .value=.natural (2-entryTag entry) ∧ after.pc=before.pc+50 ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  rw [readEntry_decompose] at fetched
  obtain ⟨firstTrace,middle,firstHead,firstLast,firstChain,firstTime,middleHeader,middleBase,middleSource,middlePC,middleOutput,firstMemory,firstBits⟩:=
    readDense_trace_safe program input before base source n k budget entry values header hbase hsource dense outside safe addressBits sourceBits
      ((natBits_mono (by omega : before.pc+39 ≤ before.pc+50)).trans counter) fetched.append_left
  have pointerValue : loadedEntryValues entry values outputCursor=.natural pointer := by
    rw [loaded_entry_preserves entry values outputCursor (Or.inr (by decide))]
    exact hpointer
  have tailFetch : FetchesCode program middle.pc readTailCode := by
    rw [middlePC]
    simpa only [readDenseCode_length] using fetched.append_right
  have middleSafe : SafeBits middle budget:=firstBits middle (List.mem_of_getLast? firstLast)
  have tailCounter : natBits (middle.pc+11) ≤ budget:=by
    rw [middlePC];simpa only [Nat.add_assoc] using counter
  obtain ⟨tail,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterTag,afterPC,afterOutput,tailMemory,tailBits⟩:=
    readTail_trace_safe program input middle base (source+6) pointer (entryTag entry) budget (loadedEntryValues entry values) middleHeader
      middleBase middleSource pointerValue (loadedEntry_tag entry values) middleSafe addressBits twoBits tailCounter tailFetch
  let after:=readTailResult middle base (entryTag entry)
  have joined:=joinTrace_spec program input firstTrace tail before middle after 705 180
    firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
  refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,afterPointer,afterTag,?_,afterOutput.trans middleOutput,
    joinTrace_memory firstTrace tail before middle base firstLast firstMemory tailMemory,
    joinTrace_invariant firstTrace tail (fun state=>SafeBits state budget) firstBits tailBits⟩
  have finalPC : after.pc=middle.pc+11 := afterPC
  omega


end PDCompute.Pack
