module

public import Paid.PDCompute_SolverReadRegion_093

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def jumpResult (before : State) (target : ℕ) : State := {before with pc:=target}

theorem jump_trace_storage (program : Program) (input : List Cell) (before : State) (target : ℕ)
    (fetch : program[before.pc]?=some (.jump target)) :
    let trace:=[before,jumpResult before target]
    trace.head?=some before ∧ trace.getLast?=some (jumpResult before target) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 30 ∧
      ∀ state ∈ trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  have control : step program input before=some (jumpResult before target) := by
    unfold step
    rw [fetch]
    rfl
  refine ⟨rfl,rfl,List.isChain_pair.mpr control,?_,?_⟩
  · simpa only [List.length_cons,List.length_nil] using time_le_length program [before,jumpResult before target]
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst state <;> exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
