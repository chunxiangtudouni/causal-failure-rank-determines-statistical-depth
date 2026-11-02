module

public import Paid.RootD27Core_EndpointCall_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Emit an actual live heap cell and advance the real pointer/count.
The payload is read by the original .load and written by .output. -/
def emitCellCode : List Instruction :=
  [.load .value .address,.output .value,.constant .flag (.natural 1),
   .natOp .add .address .address .flag,.natOp .subtract .index .index .flag]

def emitCellResult (before : State) (pointer remaining : ℕ) (value : Cell) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      before.register .value value) .flag (.natural 1)) .address (.natural (pointer+1)))
        .index (.natural remaining)
    pc:=before.pc+5
    output:=before.output++[value]}

def emitHeapCode (origin returnPC : ℕ) : List Instruction :=
  [.branchZero .index returnPC (origin+1)]++emitCellCode++[.jump origin]

theorem emitCell_length : emitCellCode.length=5 := rfl

theorem emitHeap_length (origin returnPC : ℕ) : (emitHeapCode origin returnPC).length=7 := rfl

theorem emitCell_straight : StraightCode emitCellCode := by
  intro instruction member
  simp only [emitCellCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst instruction <;> trivial

theorem emitCell_execute (input : List Cell) (before : State) (pointer remaining : ℕ) (value : Cell)
    (address : before.register .address=.natural pointer)
    (index : before.register .index=.natural (remaining+1))
    (live : pointer∈before.live) (payload : before.heap pointer=value) :
    linearExecute input emitCellCode before=some (emitCellResult before pointer remaining value) := by
  simp [emitCellCode,emitCellResult,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,address,index,live,payload]

theorem emitCell_prefix (input : List Cell) (before after : State) (pointer count : ℕ) (value : Cell)
    (address : before.register .address=.natural pointer)
    (live : pointer∈before.live) (payload : before.heap pointer=value) (bound : count<5)
    (executed : linearExecute input (emitCellCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧
      (after.output=before.output ∨ after.output=before.output++[value]) := by
  interval_cases count <;>
    simp [emitCellCode,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,address,live,payload] at executed <;>
    subst after <;> exact ⟨rfl,rfl,by first | exact Or.inl rfl | exact Or.inr rfl⟩

theorem emitHeap_guard_fetch (program : Program) (origin returnPC : ℕ)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC)) :
    program[origin]?=some (.branchZero .index returnPC (origin+1)) := by
  exact (fetched 0 (by rw [emitHeap_length]; decide)).trans (by rfl)

theorem emitHeap_cell_fetch (program : Program) (origin returnPC : ℕ)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC)) :
    FetchesCode program (origin+1) emitCellCode := by
  have layout : emitHeapCode origin returnPC=
      [.branchZero .index returnPC (origin+1)]++(emitCellCode++[.jump origin]) := by
    simp only [emitHeapCode,List.append_assoc]
  rw [layout] at fetched
  exact fetched.append_right.append_left

theorem emitHeap_jump_fetch (program : Program) (origin returnPC : ℕ)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC)) :
    program[origin+6]?=some (.jump origin) :=
  (fetched 6 (by rw [emitHeap_length]; decide)).trans (by rfl)

theorem emitHeap_guard_actual (program : Program) (input : List Cell) (before : State)
    (origin returnPC count : ℕ) (position : before.pc=origin)
    (index : before.register .index=.natural count)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤30 ∧ after={before with pc:=if count=0 then returnPC else origin+1} ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  let after : State:={before with pc:=if count=0 then returnPC else origin+1}
  have instruction:=emitHeap_guard_fetch program origin returnPC fetched
  have control : step program input before=some after := by
    simp only [step,position,instruction]
    simp [Instruction.execute,index,Cell.nat?,after]
  refine ⟨[before,after],after,rfl,rfl,List.isChain_cons_cons.mpr ⟨control,.singleton after⟩,?_,rfl,?_⟩
  · exact time_le_length program [before,after]
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst state <;> exact ⟨rfl,rfl,rfl⟩

end RootD27.Core
