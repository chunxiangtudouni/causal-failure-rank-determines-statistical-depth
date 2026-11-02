module

public import Paid.PDCompute_SolverSmallTraceMemory_061

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem HeaderMemory.trace_last {trace : List State} {before after : State} {base : ℕ}
    (memory : ∀ state ∈ trace, HeaderMemory before state base) (last : trace.getLast?=some after) :
    HeaderMemory before after base := by
  have split := List.dropLast_append_getLast? after (by rw [last]; simp)
  apply memory after
  rw [← split]
  simp

theorem joinTrace_memory (first later : List State) (before middle : State) (base : ℕ)
    (last : first.getLast?=some middle)
    (firstMemory : ∀ state ∈ first, HeaderMemory before state base)
    (laterMemory : ∀ state ∈ later, HeaderMemory middle state base) :
    ∀ state ∈ joinTrace first later, HeaderMemory before state base := by
  have split := List.dropLast_append_getLast? middle (by rw [last]; simp)
  have middleMemory := HeaderMemory.trace_last firstMemory last
  intro state member
  rcases List.mem_append.mp member with firstMember|laterMember
  · apply firstMemory state
    rw [← split]
    exact List.mem_append.mpr (Or.inl firstMember)
  · exact middleMemory.trans (laterMemory state laterMember)

theorem appendTrace_memory (trace : List State) (before after : State) (base : ℕ)
    (memory : ∀ state ∈ trace, HeaderMemory before state base) (afterMemory : HeaderMemory before after base) :
    ∀ state ∈ trace++[after], HeaderMemory before state base := by
  intro state member
  rcases List.mem_append.mp member with earlier|last
  · exact memory state earlier
  · have eq : state=after := by simpa only [List.mem_singleton] using last
    subst state
    exact afterMemory

end PDCompute.Solver
