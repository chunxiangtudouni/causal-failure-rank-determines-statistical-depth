module
public import Paid.PDCompute_Pack_CounterInit_004
public import Paid.PDCompute_Pack_Decrement_003
public import Paid.PDCompute_SolverSmallTraceMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem copyPlusOne_straight (source target : ℕ) : StraightCode (copyPlusOneCode source target) := by
  intro instruction member
  rcases List.mem_append.mp member with first|later
  · exact copySlot_straight source target instruction first
  · exact addNatSlot_straight target 1 instruction later

/-- Actual fetched initial-counter trace, with every state in Header48
footprint. This reuses the frozen literal-trace refinement. -/
theorem copyPlusOne_trace (program : Program) (input : List Cell) (before : State)
    (base source target value : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values source=.natural value)
    (fetched : FetchesCode program before.pc (copyPlusOneCode source target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (copyPlusOneResult before base source target value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤225 ∧
      Header (copyPlusOneResult before base source target value) base (Function.update values target (.natural (value+1))) ∧
      (copyPlusOneResult before base source target value).register .fresh=.natural base ∧
      (copyPlusOneResult before base source target value).pc=before.pc+14 ∧
      (copyPlusOneResult before base source target value).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have run:=copyPlusOne_execute input before base source target value values header sourceInside hbase hvalue
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input (copyPlusOneCode source target)
    (copyPlusOne_straight source target) before _ base fetched run
    (fun count bound state execute=>copyPlusOne_prefix_memory input before state base source target value values
      header sourceInside targetInside hbase hvalue count bound execute)
  have afterHeader:=copyPlusOne_header before base source target value values header sourceInside
  have firstFields:=copySlotResult_fields before base source target
  have lastFields:=addNatSlotResult_fields (copySlotResult before base source target) base target value 1
  refine ⟨trace,hh,hl,hchain,ht,afterHeader,?_,?_,(HeaderMemory.trace_last memory hl).2.2,memory⟩
  · exact lastFields.2.2.1.trans (firstFields.2.2.1.trans hbase)
  · change (addNatSlotResult (copySlotResult before base source target) base target value 1).pc=before.pc+14
    rw [lastFields.2.2.2.1,firstFields.2.2.2.1]

theorem decrement_trace (program : Program) (input : List Cell) (before : State)
    (base slot value : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (inside : slot<headerWords) (hbase : before.register .fresh=.natural base)
    (hvalue : values slot=.natural value)
    (fetched : FetchesCode program before.pc (decrementSlot slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (decrementResult before base slot value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤135 ∧
      Header (decrementResult before base slot value) base (Function.update values slot (.natural (value-1))) ∧
      (decrementResult before base slot value).register .fresh=.natural base ∧
      (decrementResult before base slot value).pc=before.pc+8 ∧
      (decrementResult before base slot value).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have run:=decrement_execute input before base slot value hbase (header.live slot inside)
    ((header.value slot inside).trans hvalue)
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input (decrementSlot slot)
    (decrementSlot_straight slot) before _ base fetched run
    (fun count bound state execute=>decrement_prefix_memory input before state base slot value values
      header inside hbase hvalue count bound execute)
  have fields:=decrement_fields before base slot value
  exact ⟨trace,hh,hl,hchain,ht,decrement_header before base slot value values header,
    fields.2.2.1.trans hbase,fields.2.2.2.1,fields.2.2.2.2,memory⟩

end PDCompute.Pack
