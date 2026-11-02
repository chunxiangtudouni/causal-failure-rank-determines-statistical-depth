module
public import Paid.PDCompute_Pack_LoadedEntry_013
public import Paid.PDCompute_SolverSmallTraceMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

def readDenseCode : List Instruction := loadSlot sourceCursor .old++denseReadBlockCode entryStart 6

theorem readDenseCode_length : readDenseCode.length=39 := rfl

/-- The actual first39 instructions of each entry iteration. The six
source cells are genuine input heap data, not a serialized-answer premise. -/
theorem readDense_trace (program : Program) (input : List Cell) (before : State) (base pointer n k : ℕ)
    (entry : MenuEntry) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hpointer : values sourceCursor=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (fetched : FetchesCode program before.pc readDenseCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤705 ∧
      Header after base (loadedEntryValues entry values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧
      after.pc=before.pc+39 ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  unfold readDenseCode at fetched
  let read:=loadSlotResult before base sourceCursor .old
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory⟩:=
    header.loadSlot_trace_memory program input sourceCursor .old (by decide) hbase fetched.append_left
  have readHeader : Header read base values := header.loadSlot_preserves sourceCursor .old
  have readBase : read.register .fresh=.natural base := (loadSlotResult_fresh before base sourceCursor .old (by decide)).trans hbase
  have readPointer : read.register .old=.natural pointer :=
    (header.loadSlot_execute input sourceCursor .old (by decide) hbase).2.trans hpointer
  have readSource : PDLower.CalibrationCompute.HeapList read pointer (denseEncodeEntry entry) := source
  have readPC : read.pc=before.pc+3 := rfl
  have tailFetch : FetchesCode program read.pc (denseReadBlockCode entryStart (denseEncodeEntry entry).length) := by
    rw [denseEncodeEntry_length]
    exact fetched.append_right
  have tailOutside : ∀ offset<(denseEncodeEntry entry).length,pointer+offset<base ∨ base+headerWords≤pointer+offset := by
    simpa only [denseEncodeEntry_length,entryWords] using outside
  obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterPC,_afterFrame,afterOutput,tailMemory⟩:=
    denseReadBlock_trace program input (denseEncodeEntry entry) read base entryStart pointer n k values readHeader
      (by rw [denseEncodeEntry_length];change 30≤48;decide) readBase readPointer readSource tailOutside tailFetch
  have tailBound : time program tail≤645 := by simpa only [denseEncodeEntry_length,entryWords] using tailTime
  have finalPointer : after.register .old=.natural (pointer+6) := by
    simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  have pc : after.pc=read.pc+36 := by simpa only [denseEncodeEntry_length,entryWords] using afterPC
  have joined:=joinTrace_spec program input firstTrace tail before read after 60 645
    firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailBound
  refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,finalPointer,?_,afterOutput,
    joinTrace_memory firstTrace tail before read base firstLast firstMemory tailMemory⟩
  omega

end PDCompute.Pack
