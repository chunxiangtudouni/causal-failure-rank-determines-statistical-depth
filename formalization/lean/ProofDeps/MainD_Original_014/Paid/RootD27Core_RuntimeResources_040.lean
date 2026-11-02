module

public import Paid.RootD27Core_RuntimeArguments_039
public import Paid.PDLower_CalibrationCompute_ReadOnly_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- Actual14 runtime-penalty heap-argument instructions, including every physical
prefix. Original input, heap, old live workspace and output are retained;
the exact PC interval is proved from actual linear execution. -/
theorem solver_runtime_arguments_actual_resources (P : Parameters) (fee : ℚ) (input : List Cell)
    (program : Program) (before : State) (returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (solverRuntimeArgumentsCode returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (solverRuntimeArgumentsResult P fee before returnPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤255 ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+(solverRuntimeArgumentsCode returnPC).length) := by
  let code:=solverRuntimeArgumentsCode returnPC
  let after:=solverRuntimeArgumentsResult P fee before returnPC
  have executed:=solverRuntimeArguments_execute P fee input before returnPC prepared
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input code
    (solverRuntimeArguments_straight returnPC) before after fetched executed
  have codeLength : code.length≤16 := by
    change 14≤16
    decide
  have readonly : code.all PDLower.CalibrationCompute.readOnly=true := by
    rfl
  have firstPC:=linearExecute_pc input code (solverRuntimeArguments_straight returnPC)
    before after executed
  have finalPC : after.pc=before.pc+(solverRuntimeArgumentsCode returnPC).length:=firstPC
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
        fun instruction inside=>solverRuntimeArguments_straight returnPC instruction (List.mem_of_mem_take inside)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      change count<(solverRuntimeArgumentsCode returnPC).length at bound
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      omega

end RootD27.Core
