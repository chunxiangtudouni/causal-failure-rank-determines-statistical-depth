module
public import Paid.PDCompute_Pack_ReadDense_025
public import Paid.PDCompute_Pack_ReadTailTrace_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def entryTag (entry : MenuEntry) : ℕ := match entry.action with
  | .finish => 0
  | .abandon => 1
  | .test _ _ => 2

theorem loadedEntry_tag (entry : MenuEntry) (values : ℕ → Cell) :
    loadedEntryValues entry values entryStart=.natural (entryTag entry) := by
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simp [loadedEntryValues,entryTag,denseEncodeEntry,denseReadHeaderValues,entryStart]

theorem readEntry_decompose : readEntryCode=readDenseCode++readTailCode := by
  simp only [readEntryCode,readDenseCode,readTailCode,tagDifferenceCode,List.append_assoc]

/-- Complete actual50-op entry preparation. In particular the branch
operand is derived from the REAL loaded tag, not supplied as an oracle. -/
theorem readEntry_trace (program : Program) (input : List Cell) (before : State) (base source pointer n k : ℕ)
    (entry : MenuEntry) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (dense : PDLower.CalibrationCompute.HeapList before source (denseEncodeEntry entry))
    (outside : ∀ offset<6,source+offset<base ∨ base+headerWords≤source+offset)
    (fetched : FetchesCode program before.pc readEntryCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤885 ∧
      Header after base (readTailValues (loadedEntryValues entry values) (source+6)) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural pointer ∧
      after.register .value=.natural (2-entryTag entry) ∧ after.pc=before.pc+50 ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  rw [readEntry_decompose] at fetched
  obtain ⟨firstTrace,middle,firstHead,firstLast,firstChain,firstTime,middleHeader,middleBase,middleSource,middlePC,middleOutput,firstMemory⟩:=
    readDense_trace program input before base source n k entry values header hbase hsource dense outside fetched.append_left
  have pointerValue : loadedEntryValues entry values outputCursor=.natural pointer := by
    rw [loaded_entry_preserves entry values outputCursor (Or.inr (by decide))]
    exact hpointer
  have tailFetch : FetchesCode program middle.pc readTailCode := by
    rw [middlePC]
    simpa only [readDenseCode_length] using fetched.append_right
  obtain ⟨tail,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterTag,afterPC,afterOutput,tailMemory⟩:=
    readTail_trace program input middle base (source+6) pointer (entryTag entry) (loadedEntryValues entry values) middleHeader
      middleBase middleSource pointerValue (loadedEntry_tag entry values) tailFetch
  let after:=readTailResult middle base (entryTag entry)
  have joined:=joinTrace_spec program input firstTrace tail before middle after 705 180
    firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
  refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,afterPointer,afterTag,?_,afterOutput.trans middleOutput,
    joinTrace_memory firstTrace tail before middle base firstLast firstMemory tailMemory⟩
  have finalPC : after.pc=middle.pc+11 := afterPC
  omega

end PDCompute.Pack
