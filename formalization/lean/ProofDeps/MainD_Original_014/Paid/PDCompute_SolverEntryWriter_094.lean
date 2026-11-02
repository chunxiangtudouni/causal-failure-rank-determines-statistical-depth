module

public import Paid.PDCompute_SolverReadRegion_093

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot loadSlotResult)
open PDMenu.ComputeFrame

def DenseFields (values : ℕ → Cell) (entry : MenuEntry) : Prop :=
  (List.range 6).map (fun offset => values (40+offset))=denseEncodeEntry entry

theorem DenseFields.value {values : ℕ → Cell} {entry : MenuEntry} (fields : DenseFields values entry)
    (offset : ℕ) (inside : offset < 6) :
    values (40+offset)=(denseEncodeEntry entry)[offset]'(by simpa only [denseEncodeEntry_length,entryWords] using inside) := by
  have mapBound : offset < ((List.range 6).map (fun i => values (40+i))).length := by
    simpa only [List.length_map,List.length_range] using inside
  have entryBound : offset < (denseEncodeEntry entry).length := by
    simpa only [denseEncodeEntry_length,entryWords] using inside
  have equal:=congrArg (fun cells : List Cell => cells[offset]?) fields
  rw [List.getElem?_eq_getElem mapBound,List.getElem?_eq_getElem entryBound] at equal
  simpa only [List.getElem_map,List.getElem_range] using Option.some.inj equal

def writeCurrentEntryCode : List Instruction := loadSlot 37 .old++denseWriteBlockCode 40 6

/-- A complete actual cell-store phase: read the real current-write
pointer from Header37 and stream the six actual Header40--45 fields.
Every older dense cell outside THIS entry is preserved at every state. -/
theorem writeCurrentEntry_trace_memory (program : Program) (input : List Cell) (before : State)
    (base pointer n k : ℕ) (values : ℕ → Cell) (entry : MenuEntry)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : values 37=.natural pointer) (fields : DenseFields values entry)
    (outside : ∀ offset < 6,pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (regionInside : cellRegion pointer 6 ⊆ workspace base n k)
    (fetch : FetchesCode program before.pc writeCurrentEntryCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 705 ∧ Header after base values ∧
      PDLower.CalibrationCompute.HeapList after pointer (denseEncodeEntry entry) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧
      after.pc=before.pc+39 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion pointer 6) := by
  let pointed:=loadSlotResult before base 37 .old
  have fetchPointer : FetchesCode program before.pc (loadSlot 37 .old) := fetch.append_left
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory⟩ :=
    header.loadSlot_trace_region program input 37 .old (by decide) hbase (cellRegion pointer 6) fetchPointer
  have pointedHeader : Header pointed base values := header
  have pointedBase : pointed.register .fresh=.natural base :=
    (loadSlotResult_fresh before base 37 .old (by decide)).trans hbase
  have pointedPointer : pointed.register .old=.natural pointer :=
    (header.loadSlot_execute input 37 .old (by decide) hbase).2.trans hpointer
  have fetchStore : FetchesCode program pointed.pc (denseWriteBlockCode 40 6) := fetch.append_right
  have contents : ∀ (offset : ℕ) (inside : offset < (denseEncodeEntry entry).length),
      values (40+offset)=(denseEncodeEntry entry)[offset] := by
    intro offset inside
    exact fields.value offset (by simpa only [denseEncodeEntry_length,entryWords] using inside)
  obtain ⟨storeTrace,after,storeHead,storeLast,storeChain,storeTime,afterHeader,afterHeap,afterBase,afterPointer,afterPC,afterOutput,storeMemory⟩ :=
    denseWriteBlock_trace program input (denseEncodeEntry entry) pointed base 40 pointer values pointedHeader
      (by rw [denseEncodeEntry_length]; change 40+6≤48; decide) pointedBase pointedPointer contents
      (by simpa only [denseEncodeEntry_length,entryWords] using outside)
      (by simpa only [denseEncodeEntry_length,entryWords] using fetchStore)
  have storeBound : time program storeTrace ≤ 645 := by simpa only [denseEncodeEntry_length,entryWords] using storeTime
  have storeRegion : ∀ state ∈ storeTrace,RegionMemory pointed state (cellRegion pointer 6) := by
    simpa only [denseEncodeEntry_length,entryWords] using storeMemory
  have joined:=joinTrace_spec program input pointerTrace storeTrace before pointed after 60 645
    pointerHead pointerLast storeHead storeLast pointerChain storeChain pointerTime storeBound
  have memory:=RegionMemory.join_trace pointerTrace storeTrace before pointed (cellRegion pointer 6) pointerLast pointerMemory storeRegion
  refine ⟨joinTrace pointerTrace storeTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterHeap,afterBase,?_,?_,(RegionMemory.trace_last memory joined.2.1).frame regionInside,afterOutput,memory⟩
  · simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  · have pointedPC : pointed.pc=before.pc+3 := rfl
    rw [denseEncodeEntry_length,entryWords,pointedPC] at afterPC
    exact afterPC

end PDCompute.Solver
