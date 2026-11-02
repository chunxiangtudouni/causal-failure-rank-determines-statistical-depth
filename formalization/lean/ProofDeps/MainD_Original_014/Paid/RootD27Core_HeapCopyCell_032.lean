module

public import Paid.RootD27Core_SolverStubCall_029
public import Paid.PDCompute_Pack_LocalRegion_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute)

/-- Six actual instructions copy ONE live source cell to a runtime
destination, create the live destination cell, advance both pointers and
decrease the runtime counter. Neither values nor counts occur in code. -/
def heapCopyCellCode : List Instruction :=
  [.load .value .address,.store .fresh .value,.constant .total (.natural 1),
   .natOp .add .address .address .total,.natOp .add .fresh .fresh .total,
   .natOp .subtract .index .index .total]

def heapCopyCellResult (before : State) (source target remaining : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update before.register .value (before.heap source)) .total (.natural 1))
        .address (.natural (source+1))) .fresh (.natural (target+1))) .index (.natural remaining)
    heap:=Function.update before.heap target (before.heap source)
    live:=insert target before.live
    pc:=before.pc+6}

def heapCopyCode (origin : ℕ) : List Instruction :=
  [.branchZero .index (origin+8) (origin+1)]++heapCopyCellCode++[.jump origin,.jumpIndirect .old]

theorem heapCopyCell_length : heapCopyCellCode.length=6 := rfl

theorem heapCopyCode_length (origin : ℕ) : (heapCopyCode origin).length=9 := rfl

theorem heapCopyCell_straight : StraightCode heapCopyCellCode := by
  simp [StraightCode,heapCopyCellCode,StraightInstruction]

theorem heapCopyCell_execute (input : List Cell) (before : State) (source target remaining : ℕ)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live) :
    linearExecute input heapCopyCellCode before=some (heapCopyCellResult before source target remaining) := by
  simp [heapCopyCellCode,heapCopyCellResult,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,address,fresh,index,live,Nat.add_assoc]

theorem heapCopyCell_prefix_memory (input : List Cell) (before after : State) (source target remaining count : ℕ)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live)
    (bound : count≤6) (actual : linearExecute input (heapCopyCellCode.take count) before=some after) :
    CellWriteMemory before after target := by
  interval_cases count <;>
    simp [heapCopyCellCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      address,fresh,index,live] at actual <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro query different
      simp only [Function.update_of_ne different]
    · first | exact Finset.subset_insert _ _ | exact Finset.Subset.refl _
    · first | exact Finset.Subset.refl _ | exact Finset.subset_insert _ _

theorem heapCopyCell_result_memory (before : State) (source target remaining : ℕ) :
    CellWriteMemory before (heapCopyCellResult before source target remaining) target := by
  refine ⟨?_,Finset.Subset.refl _,Finset.subset_insert _ _,rfl⟩
  intro query different
  simp only [heapCopyCellResult,Function.update_of_ne different]

theorem heapCopyCell_actual (program : Program) (input : List Cell) (before : State) (source target remaining : ℕ)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live)
    (fetched : FetchesCode program before.pc heapCopyCellCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (heapCopyCellResult before source target remaining) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤105 ∧
      (∀ state∈trace,CellWriteMemory before state target) := by
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input heapCopyCellCode
    heapCopyCell_straight before _ fetched (heapCopyCell_execute input before source target remaining address fresh index live)
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (heapCopyCellResult before source target remaining) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩:=prefixes state proper
    exact heapCopyCell_prefix_memory input before state source target remaining count address fresh index live
      (by simpa only [heapCopyCell_length] using bound.le) actual
  · have same : state=heapCopyCellResult before source target remaining:=List.mem_singleton.mp terminal
    subst state
    exact heapCopyCell_result_memory before source target remaining

end RootD27.Core
