module

public import Paid.RootD27Core_SaveResult_066

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute linearExecute_append)

/-- Reuse the actual original runtime input loader to recover freshB,
then physically reload the saved count/pointer. Only a static return PC
is in code; M, the descriptor and table lengths are genuine heap data. -/
def restoreSolverResultCode (returnPC : ℕ) : List Instruction :=
  solverRuntimeArgumentsCode returnPC++
    [.constant .address (.natural 47),.load .index .address,
     .constant .address (.natural 46),.load .address .address]

def restoreSolverResult (P : Parameters) (fee : ℚ) (before : State) (returnPC source count : ℕ) : State :=
  let args:=solverRuntimeArgumentsResult P fee before returnPC
  {args with
    register:=Function.update (Function.update args.register .index (.natural count)) .address (.natural source)
    pc:=before.pc+18}

theorem restoreSolverResult_length (returnPC : ℕ) : (restoreSolverResultCode returnPC).length=18:=rfl

theorem restoreSolverResult_straight (returnPC : ℕ) : StraightCode (restoreSolverResultCode returnPC) := by
  simp [restoreSolverResultCode,solverRuntimeArgumentsCode,solverHeapArgumentPrefix,StraightCode,StraightInstruction]

theorem restoreSolverResult_execute (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (returnPC source count : ℕ) (prepared : HeapList before 0 (preparedInput P fee))
    (saved : HeapList before 46 [.natural source,.natural count]) :
    linearExecute input (restoreSolverResultCode returnPC) before=
      some (restoreSolverResult P fee before returnPC source count) := by
  have sourceLive : 46∈before.live:=saved.1 0 (by change 0<2;decide)
  have countLive : 47∈before.live:=saved.1 1 (by change 1<2;decide)
  have sourceValue:=PDLower.CalibrationCompute.HeapList.value saved 0 (by change 0<2;decide)
  have countValue:=PDLower.CalibrationCompute.HeapList.value saved 1 (by change 1<2;decide)
  change before.heap 46=.natural source at sourceValue
  change before.heap 47=.natural count at countValue
  rw [restoreSolverResultCode,linearExecute_append,
    solverRuntimeArguments_execute P fee input before returnPC prepared,Option.bind_some]
  simp [linearExecute,Instruction.execute,State.set,Cell.nat?,solverRuntimeArgumentsResult,restoreSolverResult,
    sourceLive,countLive,sourceValue,countValue,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

/-- SAME actual eighteen-op trace restores the original solver base and
the real returned descriptor after comparisons. Old scratch and all heap
contents survive; no initial fresh/address/index registers are assumed. -/
theorem restore_solver_result_actual (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (returnPC source count : ℕ) (prepared : HeapList before 0 (preparedInput P fee))
    (saved : HeapList before 46 [.natural source,.natural count])
    (fetched : FetchesCode program before.pc (restoreSolverResultCode returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (restoreSolverResult P fee before returnPC source count) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤285 ∧
      (restoreSolverResult P fee before returnPC source count).register .fresh=.natural (99+2*P.certificate.M) ∧
      (restoreSolverResult P fee before returnPC source count).register .address=.natural source ∧
      (restoreSolverResult P fee before returnPC source count).register .index=.natural count ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+18) ∧
      peakCells trace≤workingCells before := by
  let code:=restoreSolverResultCode returnPC
  let after:=restoreSolverResult P fee before returnPC source count
  have run:=restoreSolverResult_execute P fee input before returnPC source count prepared saved
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input code
    (restoreSolverResult_straight returnPC) before after fetched run
  have readonly : code.all PDLower.CalibrationCompute.readOnly=true:=rfl
  have allMemory : ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,_bound,actual⟩:=prefixes state proper
      have safe : (code.take stepsTaken).all PDLower.CalibrationCompute.readOnly=true := by
        apply List.all_eq_true.mpr
        intro instruction member
        exact (List.all_eq_true.mp readonly) instruction (List.mem_of_mem_take member)
      exact PDLower.CalibrationCompute.linearReadOnly_heap input _ before state safe actual
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact ⟨rfl,rfl,rfl⟩
  have allPC : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+18 := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      have straight : StraightCode (code.take stepsTaken):=
        fun instruction member=>restoreSolverResult_straight returnPC instruction (List.mem_of_mem_take member)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      change stepsTaken<18 at bound
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      change before.pc≤before.pc+18 ∧ before.pc+18≤before.pc+18
      omega
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have memory:=allMemory state member
    unfold workingCells
    rw [memory.2.1,memory.2.2]
  refine ⟨trace,head,last,chain,cost,?_,?_,?_,allMemory,allPC,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace⟩
  · simp [restoreSolverResult,solverRuntimeArgumentsResult]
  · simp [restoreSolverResult]
  · simp [restoreSolverResult]

end RootD27.Core
