module

public import Paid.RootD27Core_EndpointOutput_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Static ROM position also names the real core-header cell. All input
values are fetched; no parameter-dependent payload occurs in the code. -/
def inputSlotCode (slot : ℕ) : List Instruction :=
  [.constant .address (.natural slot),.loadInput .value .address,.store .address .value]

def inputSlotResult (before : State) (slot : ℕ) (value : Cell) : State :=
  {before with
    register:=Function.update (Function.update before.register .address (.natural slot)) .value value
    heap:=Function.update before.heap slot value
    live:=insert slot before.live
    pc:=before.pc+3}

theorem inputSlot_length (slot : ℕ) : (inputSlotCode slot).length=3 := rfl

theorem inputSlot_straight (slot : ℕ) : StraightCode (inputSlotCode slot) := by
  simp [StraightCode,inputSlotCode,StraightInstruction]

theorem inputSlot_execute (input : List Cell) (before : State) (slot : ℕ) (value : Cell)
    (fetched : input[slot]?=some value) :
    linearExecute input (inputSlotCode slot) before=some (inputSlotResult before slot value) := by
  simp [inputSlotCode,inputSlotResult,linearExecute,Instruction.execute,State.set,Cell.nat?,fetched]

theorem inputSlot_prefix (input : List Cell) (before after : State) (slot count : ℕ)
    (bound : count<3)
    (executed : linearExecute input ((inputSlotCode slot).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [inputSlotCode,linearExecute,Instruction.execute,State.set,Cell.nat?] at executed
  all_goals
    first
    | (subst after;exact ⟨rfl,rfl,rfl⟩)
    | (obtain ⟨loaded,_,same⟩:=Option.bind_eq_some_iff.mp executed
       have eq:=Option.some.inj same
       subst after
       exact ⟨rfl,rfl,rfl⟩)

theorem inputSlot_header (before : State) (slot : ℕ) (value : Cell) (values : ℕ→Cell)
    (header : Header before 0 values) (inside : slot<headerWords) :
    Header (inputSlotResult before slot value) 0 (Function.update values slot value) ∧
      HeaderMemory before (inputSlotResult before slot value) 0 := by
  have heap : (inputSlotResult before slot value).heap=Function.update before.heap (0+slot) value := by
    simp only [inputSlotResult,Nat.zero_add]
  have live : (inputSlotResult before slot value).live=insert (0+slot) before.live := by
    simp only [inputSlotResult,Nat.zero_add]
  exact ⟨header.update slot value heap (fun address member => Finset.mem_insert_of_mem member),
    HeaderMemory.write header slot inside value heap live rfl⟩

theorem inputSlot_actual (program : Program) (input : List Cell) (before : State)
    (slot : ℕ) (value : Cell) (values : ℕ→Cell) (header : Header before 0 values)
    (inside : slot<headerWords) (payload : input[slot]?=some value)
    (fetched : FetchesCode program before.pc (inputSlotCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (inputSlotResult before slot value) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤60 ∧
      Header (inputSlotResult before slot value) 0 (Function.update values slot value) ∧
      ∀ state∈trace,HeaderMemory before state 0 := by
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input (inputSlotCode slot)
    (inputSlot_straight slot) before (inputSlotResult before slot value) fetched
    (inputSlot_execute input before slot value payload)
  have updated:=inputSlot_header before slot value values header inside
  refine ⟨trace,head,last,chain,cost,updated.1,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (inputSlotResult before slot value) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,executed⟩:=prefixes state proper
    have memory:=inputSlot_prefix input before state slot count bound executed
    exact HeaderMemory.of_unchanged 0 memory.1 memory.2.1 memory.2.2
  · have same : state=inputSlotResult before slot value := by simpa only [List.mem_singleton] using terminal
    subst state
    exact updated.2

end RootD27.Core
