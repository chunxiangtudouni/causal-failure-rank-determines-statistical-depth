module

public import Paid.RootD27Core_DenseCaller_046
public import Paid.RootD27Core_SolverStub_011
public import Paid.RootD27Core_CalibrationCaller_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- A real shared jump entry, then the complete literal solver strictly
above that entry, and the actual saved indirect return. The request log,
entry count, table, time and prefix memory all describe ONE real trace. -/
theorem solver_stub_call_dense_actual (mode : ReaderMode) (program : Program) (input : List Cell)
    (labels : RoutineLabels) (P : Parameters) (fee penalty : ℚ) (before : State)
    (base n k source returnPC : ℕ)
    (position : before.pc=labels.solveEntry) (returnSeparate : returnPC≠labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode mode (labels.solveEntry+1)))
    (fresh : before.register .fresh=.natural base) (old : before.register .old=.natural returnPC)
    (address : before.register .address=.natural source) (total : before.register .total=.rational penalty)
    (index : before.register .index=.natural n) (value : before.register .value=.natural k)
    (flag : before.register .flag=.rational fee)
    (endpoint : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38100*(P.certificate.M+1)*PDCompute.Solver.entryCount n k ∧
      Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace≤workingCells before+62*PDCompute.Solver.entryCount n k ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      DenseOriginalTable after P fee penalty base n k ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  let entered : State:={before with pc:=labels.solveEntry+1}
  have jump : step program input before=some entered := by
    simp only [step,position,stubFetch]
    rfl
  have stubChain : [before,entered].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨jump,.singleton entered⟩
  have stubTime : time program [before,entered]≤30:=time_le_length program [before,entered]
  obtain ⟨body,after,bh,bl,bc,bt,returned,memory,peak,scope,dense,root⟩:=
    solver_callee_dense_in_program mode program input (labels.solveEntry+1) bodyFetch P fee penalty entered
      base n k source returnPC rfl fresh old address total index value flag endpoint avoids
  have bodyExcluded : ∀ state∈body,state.pc≠labels.solveEntry := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [bl];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have lower:=(scope state proper).1
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      rw [returned.1]
      exact returnSeparate
  have noBody:=no_solve_entry labels body bodyExcluded
  have one:=one_solve_entry labels before penalty position total
  have joined:=joinTrace_spec program input [before,entered] body before entered after
    30 (38000*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+15)
      rfl rfl bh bl stubChain bc stubTime bt
  change Return P fee penalty n k base returnPC before after at returned
  change ∀ state∈body,RegionMemory before state (workspace base n k) at memory
  change peakCells body≤workingCells before+62*PDCompute.Solver.entryCount n k at peak
  have allMemory : ∀ state∈joinTrace [before,entered] body,RegionMemory before state (workspace base n k) := by
    intro state member
    rcases joinTrace_member member with stubMember|bodyMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at stubMember
      rcases stubMember with same|same
      · subst state
        exact .refl before _
      · subst state
        exact .refl before _
    · exact memory state bodyMember
  have allSpace : ∀ state∈joinTrace [before,entered] body,
      workingCells state≤workingCells before+62*PDCompute.Solver.entryCount n k := by
    intro state member
    rcases joinTrace_member member with stubMember|bodyMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at stubMember
      rcases stubMember with same|same
      · subst state
        omega
      · subst state
        change workingCells before≤workingCells before+62*PDCompute.Solver.entryCount n k
        omega
    · exact (workingCells_le_peak_of_member body state bodyMember).trans peak
  refine ⟨joinTrace [before,entered] body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,
    allMemory,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,?_,?_,dense,root⟩
  · have positive : 0<(P.certificate.M+1)*PDCompute.Solver.entryCount n k := by
      unfold PDCompute.Solver.entryCount
      positivity
    have budget : 30+(38000*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+15)≤
        38100*(P.certificate.M+1)*PDCompute.Solver.entryCount n k := by
      simp only [Nat.mul_assoc]
      omega
    exact joined.2.2.2.trans budget
  · change actualSolveRequests labels ([before]++body)=[penalty]
    rw [solveRequests_append,one.1,noBody.1,List.append_nil]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry ([before]++body)=1
    rw [solveEntries_append,one.2,noBody.2,Nat.add_zero]

end RootD27.Core
