module

public import Paid.PDROC_D27Prepare_Resources_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlotResult)
open PDROC.D27Prepare.Program PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Resources

theorem outputSlot_prefix_bounds (input : List Cell) (before : State) (address H B : ℕ)
    (bounded : StateBounds H B before) (fresh : before.register .fresh=.natural 0)
    (live : address∈before.live) (addressBits : 1+natBits H≤B) :
    LinearPrefixBounds input (outputSlot address) before H B := by
  let loaded := loadSlotResult before 0 address .total
  have loadRun := PDLower.CalibrationCompute.loadSlot_execute input before 0 address .total fresh
    (by simpa only [Nat.zero_add] using live)
  have inside : address<H := Finset.mem_range.mp (bounded.live live)
  have loadBound := loadSlot_prefix_bounds input before address .total H B bounded fresh live
    (address_cell_bits address H B inside addressBits)
  exact LinearPrefixBounds.append input _ _ before loaded H B loadRun loadBound
    (output_prefix_bounds input loaded .total H B (loadBound.final loadRun))

theorem outputSequence_prefix_bounds (addresses : List ℕ) (input : List Cell) (before : State)
    (memory : SlotMemory) (H B : ℕ) (matched : MemoryMatch before memory)
    (bounded : StateBounds H B before) (live : ∀ address∈addresses,address∈memory.present)
    (addressBits : 1+natBits H≤B) :
    LinearPrefixBounds input (outputSequenceCode addresses) before H B := by
  induction addresses generalizing before with
  | nil => exact LinearPrefixBounds.nil input bounded
  | cons address rest ih =>
    let middle := outputSlotResult before address (memory.value address)
    have actual := outputSlot_execute input before address (memory.value address) matched.base
      (by rw [matched.live]; exact live address (by simp)) (by rw [matched.heap])
    have first := outputSlot_prefix_bounds input before address H B bounded matched.base
      (by rw [matched.live]; exact live address (by simp)) addressBits
    have fields := outputSlotResult_fields before address (memory.value address)
    have matchedMiddle : MemoryMatch middle memory :=
      ⟨fields.1.trans matched.heap,fields.2.1.trans matched.live,fields.2.2.1.trans matched.base⟩
    have later := ih middle matchedMiddle (first.final actual)
      (fun other member => live other (by simp only [List.mem_cons]; exact Or.inr member))
    simpa only [outputSequenceCode,List.flatMap_cons] using
      LinearPrefixBounds.append input _ _ before middle H B actual first later

/-- The original final page emits its thirteen actual live cells and fetches
HALT. Every physical prefix inherits the caller's already proved bit bound. -/
theorem bounded_emitPrepared_trace (input : List Cell) (before : State) (memory : SlotMemory)
    (B : ℕ) (matched : MemoryMatch before memory) (start : before.pc=pc 45)
    (bounded : StateBounds 64 B before) (live : ∀ address<13,address∈memory.present)
    (addressBits : 1+natBits 64≤B) :
    ∃ (after : State) (trace : List State), MemoryMatch after memory ∧
      after.output=before.output++(List.range 13).map memory.value ∧
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.length=53 ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      program[after.pc]?=some .halt ∧ time program trace≤15*53 ∧
      ∀ state∈trace,StateBounds 64 B state := by
  obtain ⟨after,executed,afterMatch,afterOutput,afterPc⟩ := outputSequence_realize (List.range 13)
    input before memory matched (by simpa only [List.mem_range] using live)
  have prefixBounds := outputSequence_prefix_bounds (List.range 13) input before memory 64 B
    matched bounded (by simpa only [List.mem_range] using live) addressBits
  have length : emitPrepared.length=52 := rfl
  have fetch : FetchesCode program before.pc emitPrepared := by
    rw [start]
    exact fetches_page_part 45 (by decide) [] emitPrepared [.halt] rfl
  obtain ⟨trace,head,last,traceLength,chain,prefixes⟩ := literal_fragment_trace_length input
    emitPrepared (outputSequence_straight (List.range 13)) before after fetch executed
  refine ⟨after,trace,afterMatch,afterOutput,head,last,?_,chain,?_,?_,?_⟩
  · simpa only [length] using traceLength
  · have position : after.pc=pc 45+52 := by
      simpa only [start,outputSequence_length,List.length_range] using afterPc
    rw [position]
    exact fetches_page 45 (by decide) 52 (by decide)
  · simpa only [traceLength,length] using time_le_length program trace
  · exact prefixBounds.trace executed trace last prefixes

end PDROC.D27Prepare.Resources
