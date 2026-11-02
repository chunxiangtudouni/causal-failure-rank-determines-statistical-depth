module

public import Paid.RootD27Core_HeapSolverDispatch_018
public import Paid.PDLower_CalibrationCompute_ReadOnly_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- Original15/16 heap-argument instructions, including every physical
prefix. Original input, heap, old live workspace and output are retained;
the exact PC interval is proved from actual linear execution. -/
theorem solver_heap_arguments_actual_resources (P : Parameters) (fee : ℚ) (input : List Cell)
    (program : Program) (before : State) (useLambda : Bool) (returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (solverHeapArgumentsCode useLambda returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (solverArgumentsResult P fee before useLambda returnPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤255 ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+(solverHeapArgumentsCode useLambda returnPC).length) := by
  let code:=solverHeapArgumentsCode useLambda returnPC
  let after:=solverArgumentsResult P fee before useLambda returnPC
  have executed:=solverHeapArguments_execute P fee input before useLambda returnPC prepared
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input code
    (solverHeapArguments_straight useLambda returnPC) before after fetched executed
  have codeLength : code.length≤16 := by
    rw [solverHeapArguments_length]
    cases useLambda <;> decide
  have readonly : code.all PDLower.CalibrationCompute.readOnly=true := by
    cases useLambda <;> rfl
  have firstPC:=linearExecute_pc input code (solverHeapArguments_straight useLambda returnPC)
    before after executed
  have finalPC : after.pc=before.pc+(solverHeapArgumentsCode useLambda returnPC).length:=firstPC
  refine ⟨trace,head,last,chain,cost.trans (by omega),?_,?_⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,_bound,actual⟩:=prefixes state proper
      have safe : (code.take count).all PDLower.CalibrationCompute.readOnly=true := by
        apply List.all_eq_true.mpr
        intro instruction inside
        exact (List.all_eq_true.mp readonly) instruction (List.mem_of_mem_take inside)
      exact PDLower.CalibrationCompute.linearReadOnly_heap input _ before state safe actual
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      exact ⟨rfl,rfl,rfl⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      have straight : StraightCode (code.take count) :=
        fun instruction inside=>solverHeapArguments_straight useLambda returnPC instruction (List.mem_of_mem_take inside)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      change count<(solverHeapArgumentsCode useLambda returnPC).length at bound
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      omega

end RootD27.Core
