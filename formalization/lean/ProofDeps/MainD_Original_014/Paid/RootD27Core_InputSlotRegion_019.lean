module

public import Paid.RootD27Core_InputSlot_012
public import Paid.RootD27Endpoint_PairPrefix_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Actual input read/store without assuming a preallocated Header.
All prefixes retain old live caller data and write only the real slot. -/
theorem inputSlot_actual_region (program : Program) (input : List Cell) (before : State)
    (slot : ℕ) (value : Cell) (payload : input[slot]?=some value)
    (fetched : FetchesCode program before.pc (inputSlotCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (inputSlotResult before slot value) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤60 ∧
      ∀ state∈trace,RegionMemory before state {slot} := by
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ :=
    linearExecute_trace_time program input (inputSlotCode slot) (inputSlot_straight slot)
      before (inputSlotResult before slot value) fetched (inputSlot_execute input before slot value payload)
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (inputSlotResult before slot value) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩:=prefixes state proper
    have memory:=inputSlot_prefix input before state slot count bound actual
    exact RegionMemory.of_unchanged _ memory.1 memory.2.1 memory.2.2
  · have same : state=inputSlotResult before slot value := List.mem_singleton.mp terminal
    subst state
    exact RootD27.Endpoint.endpoint_store_region before slot value {slot} (by simp)

end RootD27.Core
