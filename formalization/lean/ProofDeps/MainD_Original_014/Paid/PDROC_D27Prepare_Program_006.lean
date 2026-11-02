module

public import Paid.PDROC_D27Prepare_Program_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

theorem input_memory_eval (c0 c1 c2 c3 c4 c5 : Cell) :
    inputSequenceEval (sixInput c0 c1 c2 c3 c4 c5) (List.range 6) emptySlotMemory=
      some (loadedInputMemory c0 c1 c2 c3 c4 c5) := by
  change inputSequenceEval (sixInput c0 c1 c2 c3 c4 c5) [0,1,2,3,4,5] emptySlotMemory=_
  simp only [inputSequenceEval,sixInput,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.bind_some,loadedInputMemory]

#check input_memory_eval

theorem initialization_eval (memory : SlotMemory) :
    slotSequenceEval initializationCommands memory=some (initializationResult memory) := by
  simp only [initializationCommands,slotSequenceEval,SlotCommand.eval,Option.bind_some,initializationResult]

#check initialization_eval

/-- Finite typed body execution is kept separate from actual code fetch. -/
theorem prologue_body_realize (c0 c1 c2 c3 c4 c5 : Cell) :
    ∃ middle : State,
      linearExecute (sixInput c0 c1 c2 c3 c4 c5) prologueBody initial=some middle ∧
      MemoryMatch middle (initializedInputMemory c0 c1 c2 c3 c4 c5) ∧
      middle.pc=87 ∧ middle.output=[] := by
  let input := sixInput c0 c1 c2 c3 c4 c5
  let baseState := ({initial with pc:=1}).set .fresh (.natural 0)
  have baseMatch : MemoryMatch baseState emptySlotMemory := ⟨rfl,rfl,rfl⟩
  have baseExecute : linearExecute input [.constant .fresh (.natural 0)] initial=some baseState := rfl
  obtain ⟨loaded,loadExecute,loadMatch,loadOutput,loadPc⟩ :=
    inputSequence_realize (List.range 6) input baseState emptySlotMemory
      (loadedInputMemory c0 c1 c2 c3 c4 c5) baseMatch (input_memory_eval c0 c1 c2 c3 c4 c5)
  obtain ⟨middle,constantExecute,middleMatch,middleOutput,middlePc⟩ :=
    slotSequence_realize initializationCommands input loaded (loadedInputMemory c0 c1 c2 c3 c4 c5)
      (initializedInputMemory c0 c1 c2 c3 c4 c5) loadMatch (initialization_eval _)
  have bodyExecute : linearExecute input prologueBody initial=some middle := by
    rw [prologueBody,PDLower.CalibrationCompute.linearExecute_append]
    rw [PDLower.CalibrationCompute.linearExecute_append,baseExecute,Option.bind_some,
      loadExecute,Option.bind_some,constantExecute]
  refine ⟨middle,bodyExecute,middleMatch,?_,middleOutput.trans (loadOutput.trans rfl)⟩
  have loadLength : (inputSequenceCode (List.range 6)).length=30 := rfl
  have constLength : (slotSequenceCode initializationCommands).length=56 := rfl
  have basePc : baseState.pc=1 := rfl
  omega

#check prologue_body_realize

end PDROC.D27Prepare.Program
