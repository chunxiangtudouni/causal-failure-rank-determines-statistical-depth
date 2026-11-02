module

public import Paid.PDCompute_CoreSearchLoop_CallWindows_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- A real entry at the head consumes the single counted occurrence.
This concerns positions, even if arbitrary non-entry states repeat. -/
theorem entry_index_zero (labels : RoutineLabels) (states : List State) (entered : State)
    (head : states.head?=some entered) (entry : entered.pc=labels.solveEntry)
    (count : entryCount labels.solveEntry states=1)
    (index : ℕ) (state : State) (found : states[index]?=some state) (position : state.pc=labels.solveEntry) :
    index=0 ∧ state=entered := by
  cases states with
  | nil => simp at head
  | cons first states =>
    have same : first=entered:=Option.some.inj head
    subst first
    simp only [entryCount,List.filter_cons,entry,beq_self_eq_true,ite_true,List.length_cons] at count
    have zero : (states.filter (fun state=>state.pc==labels.solveEntry)).length=0:=by omega
    have empty:=List.length_eq_zero_iff.mp zero
    cases index with
    | zero =>
      have same : entered=state:=Option.some.inj found
      exact ⟨rfl,same.symm⟩
    | succ index =>
      have member : state∈states:=List.mem_of_getElem? found
      have filtered : state∈states.filter (fun state=>state.pc==labels.solveEntry):=
        List.mem_filter.mpr ⟨member,by simp [position]⟩
      rw [empty] at filtered
      exact False.elim (List.not_mem_nil filtered)

/-- A producer supplies its actual common-epilogue window at index zero;
the original all-index SolverCallRefinement follows from true head/count1.
No caller-return PC is substituted for labels.solveReturn. -/
theorem refinement_of_entry_window (program : Program) (labels : RoutineLabels)
    (P : Parameters) (fee : ℚ) (constant : ℕ) (states : List State) (entered : State)
    (head : states.head?=some entered) (entry : entered.pc=labels.solveEntry)
    (count : entryCount labels.solveEntry states=1)
    (window : CallAt program labels P fee constant states 0 entered) :
    SolverCallRefinement program labels P fee constant states := by
  intro index state found position
  obtain ⟨zero,same⟩:=entry_index_zero labels states entered head entry count index state found position
  subst index
  subst state
  exact window

end PDCompute.CoreSearchLoop
