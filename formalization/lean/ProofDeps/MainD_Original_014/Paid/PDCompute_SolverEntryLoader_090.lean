module

public import Paid.PDCompute_SolverDenseHeaderFacts_080

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot loadSlotResult)
open PDMenu.ComputeFrame

def loadDenseEntryCode (pointerSlot target : ℕ) : List Instruction :=
  loadSlot pointerSlot .old++denseReadBlockCode target 6

theorem loadDenseEntryCode_length (pointerSlot target : ℕ) : (loadDenseEntryCode pointerSlot target).length=39 := by
  rw [loadDenseEntryCode,List.length_append,denseReadBlockCode_length]
  rfl

/-- The dense entry is read from the actual saved pointer in a live
Header slot, with real typed instructions before the six-cell reader.
For good and predecessor entries use the fixed pairs(35,7),(36,13). -/
theorem loadDenseEntry_trace_memory (program : Program) (input : List Cell) (before : State)
    (base pointerSlot target pointer n k : ℕ) (values : ℕ → Cell) (entry : MenuEntry)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (inside : pointerSlot < headerWords) (room : target+6 ≤ headerWords)
    (hpointer : values pointerSlot=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset < 6,pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetch : FetchesCode program before.pc (loadDenseEntryCode pointerSlot target)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 705 ∧ Header after base (denseReadHeaderValues (denseEncodeEntry entry) target values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧
      after.pc=before.pc+39 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let pointed:=loadSlotResult before base pointerSlot .old
  have fetchPointer : FetchesCode program before.pc (loadSlot pointerSlot .old) := fetch.append_left
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory⟩ :=
    header.loadSlot_trace_memory program input pointerSlot .old inside hbase fetchPointer
  have pointedBase : pointed.register .fresh=.natural base :=
    (loadSlotResult_fresh before base pointerSlot .old (by decide)).trans hbase
  have pointedPointer : pointed.register .old=.natural pointer :=
    (header.loadSlot_execute input pointerSlot .old inside hbase).2.trans hpointer
  have fetchEntry : FetchesCode program pointed.pc (denseReadBlockCode target 6) := fetch.append_right
  have pointedHeader : Header pointed base values := header
  have pointedSource : PDLower.CalibrationCompute.HeapList pointed pointer (denseEncodeEntry entry) := source
  obtain ⟨entryTrace,after,entryHead,entryLast,entryChain,entryTime,afterHeader,afterBase,afterPointer,afterPC,afterFrame,afterOutput,entryMemory⟩ :=
    denseReadBlock_trace program input (denseEncodeEntry entry) pointed base target pointer n k values
      pointedHeader (by simpa only [denseEncodeEntry_length,entryWords] using room) pointedBase pointedPointer pointedSource
      (by simpa only [denseEncodeEntry_length,entryWords] using outside)
      (by simpa only [denseEncodeEntry_length,entryWords] using fetchEntry)
  have entryBound : time program entryTrace ≤ 645 := by
    simpa only [denseEncodeEntry_length,entryWords] using entryTime
  have joined:=joinTrace_spec program input pointerTrace entryTrace before pointed after 60 645
    pointerHead pointerLast entryHead entryLast pointerChain entryChain pointerTime entryBound
  refine ⟨joinTrace pointerTrace entryTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,afterBase,?_,?_,
    (loadSlotResult_frame before base pointerSlot n k .old).trans afterFrame,afterOutput,
    joinTrace_memory pointerTrace entryTrace before pointed base pointerLast pointerMemory entryMemory⟩
  · simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  · have pointedPC : pointed.pc=before.pc+3 := rfl
    rw [denseEncodeEntry_length,entryWords,pointedPC] at afterPC
    exact afterPC

end PDCompute.Solver
