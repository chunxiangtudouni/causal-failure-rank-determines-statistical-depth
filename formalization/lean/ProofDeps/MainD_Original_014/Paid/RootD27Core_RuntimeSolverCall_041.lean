module

public import Paid.RootD27Core_RuntimeResources_040
public import Paid.RootD27Core_SolverStubCall_029
public import Paid.RootD27Core_CacheLayout_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- Real runtime-penalty argument reads, actual dispatch jump, actual common
entry and complete solver with true indirect return. The shared arrival
is removed exactly once. All resource/log conclusions use ONE trace. -/
theorem solver_runtime_from_prepared_heap_actual (P : Parameters) (fee penalty : ℚ) (input : List Cell)
    (program : Program) (labels : RoutineLabels) (before : State) (returnPC : ℕ)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (dispatchFetch : FetchesCode program before.pc (solverRuntimeDispatchCode returnPC labels.solveEntry))
    (separatePC : before.pc+(solverRuntimeArgumentsCode returnPC).length<labels.solveEntry)
    (returnSeparate : returnPC≠labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38400*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      Return P fee penalty P.certificate.stages P.tools
        (99+2*P.certificate.M) returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace (99+2*P.certificate.M) P.certificate.stages P.tools)) ∧
      peakCells trace≤workingCells before+62*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 := by
  let middle:=solverRuntimeArgumentsResult P fee before returnPC
  let entered : State:={middle with pc:=labels.solveEntry}
  change FetchesCode program before.pc (solverRuntimeArgumentsCode returnPC++[.jump labels.solveEntry]) at dispatchFetch
  obtain ⟨setup,sh,sl,sc,st,memory,pcs⟩:=solver_runtime_arguments_actual_resources P fee input program before
    returnPC prepared dispatchFetch.append_left
  have middlePC : middle.pc=before.pc+(solverRuntimeArgumentsCode returnPC).length := by
    rfl
  have jumpFetch : program[middle.pc]?=some (.jump labels.solveEntry) := by
    rw [middlePC]
    exact (dispatchFetch (solverRuntimeArgumentsCode returnPC).length (by simp)).trans (by simp)
  have jump : step program input middle=some entered := by
    simp only [step,jumpFetch]
    rfl
  have controlled:=chain_append_control program input setup middle entered sc sl jump
  have nonempty : setup≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at sh
  have dispatchHead : (setup++[entered]).head?=some before := by
    simpa only [List.head?_append_of_ne_nil setup nonempty] using sh
  have setupExcluded:=no_solve_entry labels setup (by
    intro state member
    have upper:=(pcs state member).2
    omega)
  have arrival:=one_solve_entry labels entered penalty rfl penaltyValue
  have requests : actualSolveRequests labels (setup++[entered])=[penalty] := by
    rw [solveRequests_append,setupExcluded.1,arrival.1,List.nil_append]
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry (setup++[entered])=1 := by
    rw [solveEntries_append,setupExcluded.2,arrival.2,Nat.zero_add]
  have dropped:=dispatch_dropLast_log labels (setup++[entered]) entered penalty
    (by simp) rfl penaltyValue requests count
  have endpoint : EndpointSource .liveHeap input P 96 entered := stored
  obtain ⟨body,after,bh,bl,bc,bt,returned,bodyMemory,bodyPeak,bodyRequests,bodyCount⟩:=
    solver_stub_call_actual .liveHeap program input labels P fee penalty entered
      (99+2*P.certificate.M) P.certificate.stages P.tools 96 returnPC rfl returnSeparate
      stubFetch bodyFetch rfl rfl rfl penaltyValue rfl rfl rfl endpoint
      (original_endpoint_avoids_solver P P.certificate.stages P.tools)
  have joined:=joinTrace_spec program input (setup++[entered]) body before entered after
    270 (38100*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools)
      dispatchHead (by simp) bh bl controlled.1 bc (controlled.2.trans (by omega)) bt
  change Return P fee penalty P.certificate.stages P.tools
    (99+2*P.certificate.M) returnPC before after at returned
  change ∀ state∈body,RegionMemory before state (workspace (99+2*P.certificate.M) P.certificate.stages P.tools) at bodyMemory
  change peakCells body≤workingCells before+62*PDCompute.Solver.entryCount P.certificate.stages P.tools at bodyPeak
  have allMemory : ∀ state∈joinTrace (setup++[entered]) body,
      RegionMemory before state (workspace (99+2*P.certificate.M) P.certificate.stages P.tools) := by
    intro state member
    rcases joinTrace_member member with dispatchMember|bodyMember
    · rcases List.mem_append.mp dispatchMember with setupMember|arrivalMember
      · obtain ⟨heap,live,output⟩:=memory state setupMember
        simpa only [RegionMemory,heap,live,output] using
          (RegionMemory.refl before (workspace (99+2*P.certificate.M) P.certificate.stages P.tools))
      · have same : state=entered:=List.mem_singleton.mp arrivalMember
        subst state
        exact .refl before _
    · exact bodyMemory state bodyMember
  have allSpace : ∀ state∈joinTrace (setup++[entered]) body,
      workingCells state≤workingCells before+62*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
    intro state member
    rcases joinTrace_member member with dispatchMember|bodyMember
    · rcases List.mem_append.mp dispatchMember with setupMember|arrivalMember
      · obtain ⟨_heap,live,output⟩:=memory state setupMember
        simp only [workingCells,live,output]
        omega
      · have same : state=entered:=List.mem_singleton.mp arrivalMember
        subst state
        change workingCells before≤workingCells before+62*PDCompute.Solver.entryCount P.certificate.stages P.tools
        omega
    · exact (workingCells_le_peak_of_member body state bodyMember).trans bodyPeak
  refine ⟨joinTrace (setup++[entered]) body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,
    allMemory,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,?_,?_⟩
  · have positive : 0<(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
      unfold PDCompute.Solver.entryCount
      positivity
    have budget : 270+38100*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools≤
        38400*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
      simp only [Nat.mul_assoc]
      omega
    exact joined.2.2.2.trans budget
  · change actualSolveRequests labels ((setup++[entered]).dropLast++body)=[penalty]
    rw [solveRequests_append,dropped.1,bodyRequests,List.nil_append]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry ((setup++[entered]).dropLast++body)=1
    rw [solveEntries_append,dropped.2,bodyCount,Nat.zero_add]

end RootD27.Core
