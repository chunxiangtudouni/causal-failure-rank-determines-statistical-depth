module

public import Paid.PDCompute_CoreEmit_Layout_001
public import Paid.PDCompute_SolverLinearPC_121

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)

theorem singleton_fields (before : State) (slot : ℕ) (value : Cell)
    (stored : HeapList before slot [value]) : slot∈before.live ∧ before.heap slot=value := by
  have live:=stored.1 0 (by simp)
  have actual:=HeapList.value stored 0 (by simp)
  simpa only [Nat.add_zero,List.getElem_cons_zero] using And.intro live actual

theorem pointer_straight (upper : Bool) : StraightCode (pointerCode upper) := by
  simp [StraightCode,pointerCode,StraightInstruction]

/-- All runtime dimensions and actual encoded length are physically read.
The dirty initial registers are arbitrary, and no heap cell is written. -/
theorem pointer_execute (input : List Cell) (before : State) (n k M count : ℕ) (upper : Bool)
    (dimensions : PreparedDimensions before n k M)
    (storedLength : HeapList before (lengthSlot upper) [.natural count]) :
    linearExecute input (pointerCode upper) before=some (pointerResult before n k M count upper) := by
  obtain ⟨nLive,nValue⟩:=singleton_fields before 0 (.natural n) dimensions.1
  obtain ⟨kLive,kValue⟩:=singleton_fields before 1 (.natural k) dimensions.2.1
  obtain ⟨MLive,MValue⟩:=singleton_fields before 7 (.natural M) dimensions.2.2
  obtain ⟨countLive,countValue⟩:=singleton_fields before (lengthSlot upper) (.natural count) storedLength
  cases upper <;>
    simp only [lengthSlot,Bool.false_eq_true,ite_false,ite_true] at countLive countValue
  all_goals
    simp [pointerCode,pointerResult,bufferBase,RootD27.Core.retainedTableBase,PDCompute.Solver.entryCount,lengthSlot,
      linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,nLive,kLive,MLive,nValue,kValue,MValue,
      countLive,countValue,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_assoc]
  all_goals
    funext register
    cases register <;> simp

theorem pointer_prefix_memory (input : List Cell) (before after : State) (n k M count taken : ℕ) (upper : Bool)
    (dimensions : PreparedDimensions before n k M)
    (storedLength : HeapList before (lengthSlot upper) [.natural count]) (bound : taken≤21)
    (executed : linearExecute input ((pointerCode upper).take taken) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  obtain ⟨nLive,nValue⟩:=singleton_fields before 0 (.natural n) dimensions.1
  obtain ⟨kLive,kValue⟩:=singleton_fields before 1 (.natural k) dimensions.2.1
  obtain ⟨MLive,MValue⟩:=singleton_fields before 7 (.natural M) dimensions.2.2
  obtain ⟨countLive,countValue⟩:=singleton_fields before (lengthSlot upper) (.natural count) storedLength
  interval_cases taken <;>
    simp [pointerCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      nLive,kLive,MLive,nValue,kValue,MValue,countLive,countValue] at executed <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

/-- The actual21-op pointer/length setup with full-prefix heap/live/output
preservation and real closed-PC interval, all on its actual fetched trace. -/
theorem pointer_trace (program : Program) (input : List Cell) (before : State) (n k M count : ℕ) (upper : Bool)
    (dimensions : PreparedDimensions before n k M)
    (storedLength : HeapList before (lengthSlot upper) [.natural count])
    (fetch : FetchesCode program before.pc (pointerCode upper)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pointerResult before n k M count upper) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤330 ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧
        before.pc≤state.pc ∧ state.pc≤before.pc+21 := by
  have executed:=pointer_execute input before n k M count upper dimensions storedLength
  obtain ⟨trace,head,last,chain,cost,prefixes,pcRange⟩:=PDCompute.Solver.linearExecute_trace_closedPC program input (pointerCode upper)
    (pointer_straight upper) before _ fetch executed
  refine ⟨trace,head,last,chain,?_,?_⟩
  · simpa only [pointer_length] using cost
  · intro state member
    have split:=List.dropLast_append_getLast? (pointerResult before n k M count upper) (by rw [last];simp)
    have actualPrefix : ∃ taken≤21,linearExecute input ((pointerCode upper).take taken) before=some state := by
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨taken,inside,actual⟩:=prefixes state proper
        exact ⟨taken,Nat.le_of_lt (by simpa only [pointer_length] using inside),actual⟩
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact ⟨21,le_refl _,executed⟩
    obtain ⟨taken,inside,actual⟩:=actualPrefix
    have memory:=pointer_prefix_memory input before state n k M count taken upper dimensions storedLength inside actual
    exact ⟨memory.1,memory.2.1,memory.2.2,by simpa only [pointer_length] using pcRange state member⟩

end PDCompute.CoreEmit
