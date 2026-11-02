module

public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- The actual straight-line trace carries BOTH the previously used
successful-prefix witnesses and the exact closed PC interval. It is not
an assertion about arbitrary traces that might continue into a caller. -/
theorem linearExecute_trace_closedPC (program : Program) (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State) (fetch : FetchesCode program before.pc code)
    (execute : linearExecute input code before=some after) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*(code.length+1) ∧
      (∀ state ∈ trace.dropLast,∃ count < code.length,linearExecute input (code.take count) before=some state) ∧
      ∀ state ∈ trace,before.pc ≤ state.pc ∧ state.pc ≤ before.pc+code.length := by
  obtain ⟨trace,head,last,chain,bound,prefixes⟩:=linearExecute_trace_time program input code straight before after fetch execute
  refine ⟨trace,head,last,chain,bound,prefixes,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? after (by rw [last]; simp)
  rw [← split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,countBound,run⟩:=prefixes state proper
    have prefixStraight : StraightCode (code.take count) :=
      fun instruction inside => straight instruction (List.mem_of_mem_take inside)
    have pc:=linearExecute_pc input (code.take count) prefixStraight before state run
    have lengthBound : (code.take count).length ≤ code.length := List.length_take_le' _ _
    omega
  · have same : state=after := List.mem_singleton.mp terminal
    subst state
    have pc:=linearExecute_pc input code straight before after execute
    omega

end PDCompute.Solver
