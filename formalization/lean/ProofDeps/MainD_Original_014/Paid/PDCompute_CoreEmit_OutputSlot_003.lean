module

public import Paid.PDCompute_CoreEmit_Pointer_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)

def outputSlotResult (before : State) (slot : ℕ) (value : Cell) : State:=
  {before with
    register:=Function.update (Function.update before.register .address (.natural slot)) .value value
    pc:=before.pc+3
    output:=before.output++[value]}

theorem outputSlot_straight (slot : ℕ) : StraightCode (outputSlotCode slot) := by
  simp [StraightCode,outputSlotCode,StraightInstruction]

theorem outputSlot_execute (input : List Cell) (before : State) (slot : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) :
    linearExecute input (outputSlotCode slot) before=some (outputSlotResult before slot value) := by
  have physical:=singleton_fields before slot value stored
  simp [outputSlotCode,outputSlotResult,linearExecute,Instruction.execute,State.set,Cell.nat?,physical.1,physical.2]

theorem outputSlot_prefix (input : List Cell) (before after : State) (slot taken : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) (inside : taken≤3)
    (executed : linearExecute input ((outputSlotCode slot).take taken) before=some after) :
    RootD27.Core.EmittedPrefix before [value] after := by
  have physical:=singleton_fields before slot value stored
  interval_cases taken <;>
    simp [outputSlotCode,linearExecute,Instruction.execute,State.set,Cell.nat?,physical.1,physical.2] at executed <;>
    subst after
  all_goals
    first
    | exact ⟨rfl,rfl,[],[value],rfl,(List.append_nil before.output).symm⟩
    | exact ⟨rfl,rfl,[value],[],rfl,rfl⟩

/-- A real three-op heap read and output, with every-prefix exact output
prefix and complete heap/live preservation on the SAME actual trace. -/
theorem outputSlot_trace (program : Program) (input : List Cell) (before : State) (slot : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) (fetch : FetchesCode program before.pc (outputSlotCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (outputSlotResult before slot value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      ∀ state∈trace,RootD27.Core.EmittedPrefix before [value] state ∧
        before.pc≤state.pc ∧ state.pc≤before.pc+3 := by
  have executed:=outputSlot_execute input before slot value stored
  obtain ⟨trace,head,last,chain,cost,prefixes,pcRange⟩:=PDCompute.Solver.linearExecute_trace_closedPC program input (outputSlotCode slot)
    (outputSlot_straight slot) before _ fetch executed
  refine ⟨trace,head,last,chain,?_,?_⟩
  · simpa only [outputSlot_length] using cost
  · intro state member
    have split:=List.dropLast_append_getLast? (outputSlotResult before slot value) (by rw [last];simp)
    have actualPrefix : ∃ taken≤3,linearExecute input ((outputSlotCode slot).take taken) before=some state := by
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨taken,inside,actual⟩:=prefixes state proper
        exact ⟨taken,Nat.le_of_lt (by simpa only [outputSlot_length] using inside),actual⟩
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact ⟨3,le_refl _,executed⟩
    obtain ⟨taken,inside,actual⟩:=actualPrefix
    exact ⟨outputSlot_prefix input before state slot taken value stored inside actual,
      by simpa only [outputSlot_length] using pcRange state member⟩

end PDCompute.CoreEmit
