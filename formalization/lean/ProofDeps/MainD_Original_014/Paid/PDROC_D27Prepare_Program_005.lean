module

public import Paid.PDROC_D27Prepare_Program_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- Exactly the six original input cells, in their original order. -/
def sixInput (c0 c1 c2 c3 c4 c5 : Cell) : List Cell := [c0,c1,c2,c3,c4,c5]

def emptySlotMemory : SlotMemory := ⟨fun _ => .natural 0,∅⟩

def loadedInputMemory (c0 c1 c2 c3 c4 c5 : Cell) : SlotMemory :=
  ((((((emptySlotMemory.write 0 c0).write 1 c1).write 2 c2).write 3 c3).write 4 c4).write 5 c5)

def initializationCommands : List SlotCommand :=
  [.constant 13 (.natural 0),.constant 14 (.natural 1),.constant 15 (.natural 2),
    .constant 16 (.rational 0),.constant 17 (.rational 1),.constant 18 (.rational 2),
    .constant 19 (.rational 3),.constant 20 (.rational 4),.constant 21 (.rational (1/2)),
    .constant 6 (.natural 1),.constant 7 (.natural 0),.constant 8 (.natural 1),
    .constant 9 (.natural 1),.constant 10 (.natural 0)]

def initializationResult (memory : SlotMemory) : SlotMemory :=
  (((((((((((((((memory).write 13 (.natural 0)).write 14 (.natural 1)).write 15 (.natural 2)).write
    16 (.rational 0)).write 17 (.rational 1)).write 18 (.rational 2)).write 19 (.rational 3)).write
    20 (.rational 4)).write 21 (.rational (1/2))).write 6 (.natural 1)).write 7 (.natural 0)).write
    8 (.natural 1)).write 9 (.natural 1)).write 10 (.natural 0))

#check initializationResult

def initializedInputMemory (c0 c1 c2 c3 c4 c5 : Cell) : SlotMemory :=
  initializationResult (loadedInputMemory c0 c1 c2 c3 c4 c5)

def prologueBody : List Instruction :=
  [.constant .fresh (.natural 0)]++inputSequenceCode (List.range 6)++slotSequenceCode initializationCommands

#check prologueBody

theorem prologue_decompose : prologue=prologueBody++go 1 := rfl

#check prologue_decompose

theorem prologueBody_length : prologueBody.length=87 := rfl

#check prologueBody_length

theorem prologueBody_straight : StraightCode prologueBody := by
  intro instruction member
  simp only [prologueBody,List.mem_append,List.mem_singleton] at member
  rcases member with (h|h)|h
  · subst instruction; trivial
  · exact inputSequence_straight _ instruction h
  · exact slotSequence_straight _ instruction h

/-- Every actual body-trace member is an executed prefix, including its
endpoint. This adds no ghost transitions to the original trace. -/
theorem body_trace_prefix (input : List Cell) (code : List Instruction) (before after : State)
    (trace : List State) (last : trace.getLast?=some after)
    (execute : linearExecute input code before=some after)
    (strict : ∀ state ∈ trace.dropLast, ∃ count < code.length,
      linearExecute input (code.take count) before=some state) :
    ∀ state ∈ trace, ∃ count ≤ code.length,
      linearExecute input (code.take count) before=some state := by
  have split : trace.dropLast++[after]=trace := List.dropLast_append_getLast? after (by rw [last]; simp)
  intro state member
  rw [←split,List.mem_append,List.mem_singleton] at member
  rcases member with member|equal
  · obtain ⟨count,less,prefixRun⟩ := strict state member
    exact ⟨count,less.le,prefixRun⟩
  · subst state
    exact ⟨code.length,le_rfl,by simpa using execute⟩


#check prologue_decompose
#check prologueBody_length
#check body_trace_prefix

end PDROC.D27Prepare.Program
