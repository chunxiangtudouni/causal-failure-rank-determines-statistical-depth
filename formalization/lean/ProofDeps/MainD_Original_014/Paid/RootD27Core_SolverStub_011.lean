module

public import Paid.RootD27Core_SolverDispatch_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDMenu.ComputeFrame

/-- A common actual solver entry stub has one genuine entry state,
then transfers to the located DP body strictly above that label. -/
theorem solverStub_actual (program : Program) (input : List Cell) (labels : RoutineLabels)
    (before : State) (penalty : ℚ) (position : before.pc=labels.solveEntry)
    (value : before.register .total=.rational penalty)
    (fetched : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤30 ∧ after={before with pc:=labels.solveEntry+1} ∧
      actualSolveRequests labels trace=[penalty] ∧ entryCount labels.solveEntry trace=1 := by
  let after : State:={before with pc:=labels.solveEntry+1}
  have control : step program input before=some after := by
    simp only [step,position,fetched]
    rfl
  have one:=one_solve_entry labels before penalty position value
  have none:=no_solve_entry labels [after] (by
    intro state member
    have same : state=after := List.mem_singleton.mp member
    subst state
    change labels.solveEntry+1≠labels.solveEntry
    omega)
  refine ⟨[before,after],after,rfl,rfl,List.isChain_cons_cons.mpr ⟨control,.singleton after⟩,
    time_le_length program [before,after],rfl,?_,?_⟩
  · have split : [before,after]=[before]++[after] := rfl
    rw [split,solveRequests_append,one.1,none.1,List.append_nil]
  · have split : [before,after]=[before]++[after] := rfl
    rw [split,solveEntries_append,one.2,none.2,Nat.add_zero]

/-- Remove the shared final arrival exactly once before joining an
actual dispatch trace to its actual solver continuation. -/
theorem dispatch_dropLast_log (labels : RoutineLabels) (trace : List State) (arrival : State) (penalty : ℚ)
    (last : trace.getLast?=some arrival) (position : arrival.pc=labels.solveEntry)
    (value : arrival.register .total=.rational penalty)
    (requests : actualSolveRequests labels trace=[penalty])
    (count : entryCount labels.solveEntry trace=1) :
    actualSolveRequests labels trace.dropLast=[] ∧ entryCount labels.solveEntry trace.dropLast=0 := by
  have split:=List.dropLast_append_getLast? arrival (by rw [last];simp)
  have single:=one_solve_entry labels arrival penalty position value
  have combined : actualSolveRequests labels trace.dropLast++[penalty]=[]++[penalty] := by
    calc
      _=actualSolveRequests labels (trace.dropLast++[arrival]) := by rw [solveRequests_append,single.1]
      _=actualSolveRequests labels trace := congrArg (actualSolveRequests labels) split
      _=[penalty] := requests
      _=[]++[penalty] := rfl
  constructor
  · have length:=congrArg List.length combined
    simp only [List.length_append,List.length_cons,List.length_nil] at length
    exact List.length_eq_zero_iff.mp (by omega)
  · have total : entryCount labels.solveEntry trace.dropLast+1=1 := by
      calc
        _=entryCount labels.solveEntry (trace.dropLast++[arrival]) := by rw [solveEntries_append,single.2]
        _=entryCount labels.solveEntry trace := congrArg (entryCount labels.solveEntry) split
        _=1 := count
    omega

end RootD27.Core
