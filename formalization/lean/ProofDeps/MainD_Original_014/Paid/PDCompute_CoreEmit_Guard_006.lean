module

public import Paid.PDCompute_CoreEmit_Pointer_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)

def guardLoadCode : List Instruction:=
  [.constant .address (.natural 13),.load .index .address]

def guardLoadResult (before : State) (tag : ℕ) : State:=
  {before with
    register:=Function.update (Function.update before.register .address (.natural 13)) .index (.natural tag)
    pc:=before.pc+2}

theorem guardLoad_length : guardLoadCode.length=2:=rfl
theorem guardLoad_straight : StraightCode guardLoadCode := by
  simp [StraightCode,guardLoadCode,StraightInstruction]

theorem guardLoad_execute (input : List Cell) (before : State) (tag : ℕ)
    (stored : HeapList before 13 [.natural tag]) :
    linearExecute input guardLoadCode before=some (guardLoadResult before tag) := by
  have physical:=singleton_fields before 13 (.natural tag) stored
  simp [guardLoadCode,guardLoadResult,linearExecute,Instruction.execute,State.set,Cell.nat?,physical.1,physical.2]

theorem guardLoad_prefix_memory (input : List Cell) (before after : State) (tag taken : ℕ)
    (stored : HeapList before 13 [.natural tag]) (inside : taken≤2)
    (executed : linearExecute input (guardLoadCode.take taken) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have physical:=singleton_fields before 13 (.natural tag) stored
  interval_cases taken <;>
    simp [guardLoadCode,linearExecute,Instruction.execute,State.set,Cell.nat?,physical.1,physical.2] at executed <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem guardLoad_trace (program : Program) (input : List Cell) (before : State) (tag : ℕ)
    (stored : HeapList before 13 [.natural tag]) (fetch : FetchesCode program before.pc guardLoadCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (guardLoadResult before tag) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤45 ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  have executed:=guardLoad_execute input before tag stored
  obtain ⟨trace,head,last,chain,cost,prefixes,_⟩:=PDCompute.Solver.linearExecute_trace_closedPC program input guardLoadCode
    guardLoad_straight before _ fetch executed
  refine ⟨trace,head,last,chain,?_,?_⟩
  · simpa only [guardLoad_length] using cost
  · intro state member
    have split:=List.dropLast_append_getLast? (guardLoadResult before tag) (by rw [last];simp)
    have actualPrefix : ∃ taken≤2,linearExecute input (guardLoadCode.take taken) before=some state := by
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨taken,inside,actual⟩:=prefixes state proper
        exact ⟨taken,Nat.le_of_lt (by simpa only [guardLoad_length] using inside),actual⟩
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact ⟨2,le_refl _,executed⟩
    obtain ⟨taken,inside,actual⟩:=actualPrefix
    exact guardLoad_prefix_memory input before state tag taken stored inside actual

/-- The tag is read again from actual heap13 and a genuine branch runs.
No semantic tag is inserted into the code or assumed in a register. -/
theorem guard_trace (program : Program) (input : List Cell) (origin returnPC : ℕ) (before : State) (tag : ℕ)
    (position : before.pc=origin) (stored : HeapList before 13 [.natural tag])
    (fetch : FetchesCode program origin (stateGuardCode (origin+3) returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      after.pc=(if tag=0 then returnPC else origin+3) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  let loaded:=guardLoadResult before tag
  let after : State:={loaded with pc:=if tag=0 then returnPC else origin+3}
  have literal : FetchesCode program origin (guardLoadCode++[.branchZero .index returnPC (origin+3)]) := fetch
  have loadFetch : FetchesCode program before.pc guardLoadCode := by rw [position];exact literal.append_left
  obtain ⟨loading,loadHead,loadLast,loadChain,loadTime,loadMemory⟩:=guardLoad_trace program input before tag stored loadFetch
  have instruction : program[origin+2]?=some (.branchZero .index returnPC (origin+3)) :=
    (fetch 2 (by rw [stateGuard_length];decide)).trans (by rfl)
  have loadedAt : loaded.pc=origin+2 := by change before.pc+2=origin+2;rw [position]
  have loadedIndex : loaded.register .index=.natural tag:=rfl
  have control : step program input loaded=some after := by
    simp only [step,loadedAt,instruction]
    simp [Instruction.execute,loadedIndex,Cell.nat?,after]
  have branchChain : [loaded,after].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨control,.singleton after⟩
  have branchTime : time program [loaded,after]≤30:=time_le_length program [loaded,after]
  have branchMemory : ∀ state∈[loaded,after],state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst state <;> exact ⟨rfl,rfl,rfl⟩
  have joined:=joinTrace_spec program input loading [loaded,after] before loaded after 45 30
    loadHead loadLast rfl rfl loadChain branchChain loadTime branchTime
  refine ⟨joinTrace loading [loaded,after],after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,rfl,rfl,rfl,rfl,?_⟩
  intro state member
  rcases RootD27.Core.joinTrace_member member with loadingState|branching
  · exact loadMemory state loadingState
  · exact branchMemory state branching

end PDCompute.CoreEmit
