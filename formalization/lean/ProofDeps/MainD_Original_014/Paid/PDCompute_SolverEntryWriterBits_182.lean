module

public import Paid.PDCompute_SolverEntryWriter_094
public import Paid.PDCompute_Pack_DenseWriteBlockBits_073
public import Paid.PDCompute_Pack_SlotBitTrace_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

/-- Original39-op saved-pointer and six REAL dense field stores.
Copied data are bounded by the actual incoming SafeBits; no guessed
action-level or machine-answer bound is imposed. -/
theorem writeCurrentEntry_trace_bits (program : Program) (input : List Cell) (before : State)
    (base pointer n k budget : ℕ) (values : ℕ → Cell) (entry : MenuEntry)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hpointer : values 37=.natural pointer) (fields : DenseFields values entry)
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (regionInside : cellRegion pointer 6⊆workspace base n k) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pointerBits : 1+natBits (pointer+6)≤budget)
    (counter : natBits (before.pc+39)≤budget) (fetch : FetchesCode program before.pc writeCurrentEntryCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤705 ∧
      Header after base values ∧ PDLower.CalibrationCompute.HeapList after pointer (denseEncodeEntry entry) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧ after.pc=before.pc+39 ∧
      Frame before after base n k ∧ after.output=before.output ∧ (∀ state∈trace,RegionMemory before state (cellRegion pointer 6)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let pointed:=loadSlotResult before base 37 .old
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have pointerRun:=(header.loadSlot_execute input 37 .old (by decide) fresh).1
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerResources⟩:=
    PDCompute.Pack.linearExecute_trace_invariant program input (loadSlot 37 .old) (loadSlot_straight 37 .old) before pointed fetch.append_left pointerRun
      (fun state=>RegionMemory before state (cellRegion pointer 6) ∧ RootD27.Bits.SafeBits state budget) (by
        intro count bound state executed
        have memory:=loadSlot_prefix_memory input before state base 37 .old fresh (header.live 37 (by decide)) count bound executed
        exact ⟨RegionMemory.of_unchanged _ memory.1 memory.2.1 memory.2.2,
          RootD27.Bits.loadSlot_prefix_safe input before state base 37 budget count .old safe fresh (header.live 37 (by decide))
            (slotBits 37 (by decide)) ((natBits_mono (by omega : before.pc+3≤before.pc+39)).trans counter) bound executed⟩)
  have pointerRegion : ∀ state∈pointerTrace,RegionMemory before state (cellRegion pointer 6) := fun state member=>(pointerResources state member).1
  have pointerSafe : ∀ state∈pointerTrace,RootD27.Bits.SafeBits state budget := fun state member=>(pointerResources state member).2
  have pointedHeader : Header pointed base values := header
  have pointedBase : pointed.register .fresh=.natural base := (loadSlotResult_fresh before base 37 .old (by decide)).trans fresh
  have pointedPointer : pointed.register .old=.natural pointer := (header.loadSlot_execute input 37 .old (by decide) fresh).2.trans hpointer
  have storeFetch : FetchesCode program pointed.pc (denseWriteBlockCode 40 6) := fetch.append_right
  have contents : ∀ (offset : ℕ) (inside : offset<(denseEncodeEntry entry).length),values (40+offset)=(denseEncodeEntry entry)[offset] := by
    intro offset inside
    exact fields.value offset (by simpa only [denseEncodeEntry_length,entryWords] using inside)
  have storeCounter : natBits (pointed.pc+6*(denseEncodeEntry entry).length)≤budget := by
    simpa only [denseEncodeEntry_length,entryWords,pointed,loadSlotResult,Nat.add_assoc] using counter
  obtain ⟨storeTrace,after,storeHead,storeLast,storeChain,storeTime,afterHeader,afterHeap,afterBase,afterPointer,afterPC,afterOutput,storeMemory,storeSafe⟩:=
    PDCompute.Pack.denseWriteBlock_trace_safe program input (denseEncodeEntry entry) pointed base 40 pointer budget values pointedHeader
      (by rw [denseEncodeEntry_length]; change 40+6≤48; decide) pointedBase pointedPointer contents
      (by simpa only [denseEncodeEntry_length,entryWords] using outside) (pointerSafe pointed (List.mem_of_getLast? pointerLast)) slotBits
      (by simpa only [denseEncodeEntry_length,entryWords] using pointerBits) storeCounter
      (by simpa only [denseEncodeEntry_length,entryWords] using storeFetch)
  have storeBound : time program storeTrace≤645 := by simpa only [denseEncodeEntry_length,entryWords] using storeTime
  have storeRegion : ∀ state∈storeTrace,RegionMemory pointed state (cellRegion pointer 6) := by simpa only [denseEncodeEntry_length,entryWords] using storeMemory
  have joined:=joinTrace_spec program input pointerTrace storeTrace before pointed after 60 645 pointerHead pointerLast storeHead storeLast pointerChain storeChain pointerTime storeBound
  have allMemory:=RegionMemory.join_trace pointerTrace storeTrace before pointed (cellRegion pointer 6) pointerLast pointerRegion storeRegion
  refine ⟨joinTrace pointerTrace storeTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,afterHeap,afterBase,?_,?_,
    (RegionMemory.trace_last allMemory joined.2.1).frame regionInside,afterOutput,allMemory,
    PDCompute.Pack.joinTrace_invariant pointerTrace storeTrace (fun state=>RootD27.Bits.SafeBits state budget) pointerSafe storeSafe⟩
  · simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  · simpa only [denseEncodeEntry_length,entryWords,pointed,loadSlotResult,Nat.add_assoc] using afterPC

end PDCompute.Solver
