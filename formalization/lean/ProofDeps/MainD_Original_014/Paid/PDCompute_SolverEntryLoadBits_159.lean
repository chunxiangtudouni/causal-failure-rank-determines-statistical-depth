module

public import Paid.PDCompute_SolverEntryLoader_090
public import Paid.PDCompute_Pack_DenseReadBlockBits_072
public import Paid.PDCompute_Pack_SlotBitTrace_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

/-- Original090 generic39-op real saved-pointer+dense6 loader, reusing
the frozen Pack072 actual reader primitive without redefining it. -/
theorem loadDenseEntry_trace_bits (program : Program) (input : List Cell) (before : State)
    (base pointerSlot target pointer n k budget : ℕ) (values : ℕ → Cell) (entry : MenuEntry)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (inside : pointerSlot<headerWords) (room : target+6≤headerWords) (hpointer : values pointerSlot=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pointerBits : 1+natBits (pointer+6)≤budget) (pcBits : natBits (before.pc+39)≤budget)
    (fetch : FetchesCode program before.pc (loadDenseEntryCode pointerSlot target)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤705 ∧
      Header after base (denseReadHeaderValues (denseEncodeEntry entry) target values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+6) ∧ after.pc=before.pc+39 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let pointed:=loadSlotResult before base pointerSlot .old
  have slotBits (slot : ℕ) (valid : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory,pointerSafe⟩:=
    PDCompute.Pack.loadSlot_trace_safe program input before base pointerSlot budget .old values header inside fresh safe (slotBits pointerSlot inside)
      ((natBits_mono (by omega : before.pc+3≤before.pc+39)).trans pcBits) fetch.append_left
  have pointedBase : pointed.register .fresh=.natural base := (loadSlotResult_fresh before base pointerSlot .old (by decide)).trans fresh
  have pointedPointer : pointed.register .old=.natural pointer := (header.loadSlot_execute input pointerSlot .old inside fresh).2.trans hpointer
  have pointedHeader : Header pointed base values := header
  have pointedSource : PDLower.CalibrationCompute.HeapList pointed pointer (denseEncodeEntry entry) := source
  have pointedBound:=pointerSafe pointed (List.mem_of_getLast? pointerLast)
  have counter : natBits (pointed.pc+6*(denseEncodeEntry entry).length)≤budget := by
    rw [denseEncodeEntry_length,entryWords]
    change natBits (before.pc+3+6*6)≤budget
    simpa only [Nat.add_assoc] using pcBits
  have fetchEntry : FetchesCode program pointed.pc (denseReadBlockCode target 6) := fetch.append_right
  obtain ⟨entryTrace,after,entryHead,entryLast,entryChain,entryTime,afterHeader,afterBase,afterPointer,afterPC,afterFrame,afterOutput,entryMemory,entrySafe⟩:=
    PDCompute.Pack.denseReadBlock_trace_safe program input (denseEncodeEntry entry) pointed base target pointer n k budget values pointedHeader
      (by simpa only [denseEncodeEntry_length,entryWords] using room) pointedBase pointedPointer pointedSource
      (by simpa only [denseEncodeEntry_length,entryWords] using outside) pointedBound slotBits
      (by simpa only [denseEncodeEntry_length,entryWords] using pointerBits) counter
      (by simpa only [denseEncodeEntry_length,entryWords] using fetchEntry)
  have entryBound : time program entryTrace≤645 := by simpa only [denseEncodeEntry_length,entryWords] using entryTime
  have joined:=joinTrace_spec program input pointerTrace entryTrace before pointed after 60 645 pointerHead pointerLast entryHead entryLast
    pointerChain entryChain pointerTime entryBound
  refine ⟨joinTrace pointerTrace entryTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,afterBase,?_,?_,
    (loadSlotResult_frame before base pointerSlot n k .old).trans afterFrame,afterOutput,
    joinTrace_memory pointerTrace entryTrace before pointed base pointerLast pointerMemory entryMemory,
    PDCompute.Pack.joinTrace_invariant pointerTrace entryTrace (fun state=>RootD27.Bits.SafeBits state budget) pointerSafe entrySafe⟩
  · simpa only [denseEncodeEntry_length,entryWords] using afterPointer
  · have pointedPC : pointed.pc=before.pc+3 := rfl
    rw [denseEncodeEntry_length,entryWords,pointedPC] at afterPC
    simpa only [Nat.add_assoc] using afterPC

end PDCompute.Solver
