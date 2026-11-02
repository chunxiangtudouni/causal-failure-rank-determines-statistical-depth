module

public import Paid.RootD27Core_SearchScalarFrame_065

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- Save the actual returned pointer/count before scalar comparisons
reuse registers. Both values come from the real solver registers. -/
def saveSolverResultCode : List Instruction :=
  [.constant .total (.natural 46),.store .total .address,
   .constant .total (.natural 47),.store .total .index,.constant .fresh (.natural 0)]

def saveSolverResult (before : State) (source count : ℕ) : State :=
  {before with
    register:=Function.update (Function.update before.register .total (.natural 47)) .fresh (.natural 0)
    heap:=Function.update (Function.update before.heap 46 (.natural source)) 47 (.natural count)
    live:=insert 47 (insert 46 before.live)
    pc:=before.pc+5}

theorem saveSolverResult_length : saveSolverResultCode.length=5:=rfl

theorem saveSolverResult_straight : StraightCode saveSolverResultCode := by
  simp [saveSolverResultCode,StraightCode,StraightInstruction]

theorem saveSolverResult_execute (input : List Cell) (before : State) (source count : ℕ)
    (address : before.register .address=.natural source) (index : before.register .index=.natural count) :
    linearExecute input saveSolverResultCode before=some (saveSolverResult before source count) := by
  simp [saveSolverResultCode,saveSolverResult,linearExecute,Instruction.execute,State.set,Cell.nat?,address,index,Nat.add_assoc]

theorem saveSolverResult_prefix_memory (input : List Cell) (before after : State) (source count stepsTaken : ℕ)
    (address : before.register .address=.natural source) (index : before.register .index=.natural count)
    (bound : stepsTaken≤5)
    (actual : linearExecute input (saveSolverResultCode.take stepsTaken) before=some after) :
    RegionMemory before after {46,47} := by
  interval_cases stepsTaken <;>
    simp [saveSolverResultCode,linearExecute,Instruction.execute,State.set,Cell.nat?,address,index] at actual <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro query outside
      have q46 : query≠46:=by intro same;subst query;simp at outside
      have q47 : query≠47:=by intro same;subst query;simp at outside
      simp_all
    · intro query member
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at member ⊢
      tauto
    · first
      | exact Finset.Subset.refl _
      | exact Finset.subset_insert _ _
      | exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

theorem saveSolverResult_saved (before : State) (source count : ℕ) :
    HeapList (saveSolverResult before source count) 46 [.natural source,.natural count] := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    change offset<2 at inside
    interval_cases offset <;> simp [saveSolverResult]
  · intro offset inside
    change offset<2 at inside
    interval_cases offset <;> simp [saveSolverResult]

/-- ONE actual five-op save/reset trace, including exact PC interval and
all-prefix write region. No descriptor or fresh0 premise is supplied. -/
theorem save_solver_result_actual (program : Program) (input : List Cell) (before : State)
    (source count : ℕ) (address : before.register .address=.natural source)
    (index : before.register .index=.natural count)
    (fetched : FetchesCode program before.pc saveSolverResultCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (saveSolverResult before source count) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤90 ∧
      (∀ state∈trace,RegionMemory before state {46,47}) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5) ∧
      peakCells trace≤workingCells before+2 := by
  let after:=saveSolverResult before source count
  have run:=saveSolverResult_execute input before source count address index
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input saveSolverResultCode
    saveSolverResult_straight before after fetched run
  have allMemory : ∀ state∈trace,RegionMemory before state {46,47} := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      exact saveSolverResult_prefix_memory input before state source count stepsTaken address index bound.le actual
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact saveSolverResult_prefix_memory input before after source count 5 address index (by decide) run
  have allPC : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5 := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      have straight : StraightCode (saveSolverResultCode.take stepsTaken):=
        fun instruction member=>saveSolverResult_straight instruction (List.mem_of_mem_take member)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      change stepsTaken<5 at bound
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      change before.pc≤before.pc+5 ∧ before.pc+5≤before.pc+5
      omega
  have regionCard : ({46,47} : Finset ℕ).card=2:=by decide
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before+2 := by
    intro state member
    have bound:=(allMemory state member).workingCells_le
    rw [regionCard] at bound
    exact bound
  exact ⟨trace,head,last,chain,cost,allMemory,allPC,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace⟩

end RootD27.Core
