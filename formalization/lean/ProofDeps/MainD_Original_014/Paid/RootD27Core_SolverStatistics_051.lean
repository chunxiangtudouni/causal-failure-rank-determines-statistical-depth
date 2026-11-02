module

public import Paid.RootD27Core_DenseStatistics_050
public import Paid.RootD27Core_DenseRuntimeCall_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- A real arbitrary runtime penalty request, complete original solver,
true indirect return, and physical root-statistics reads in ONE trace.
Neither the table nor its risk/cost record is supplied as input. -/
theorem solver_runtime_statistics_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (target returnPC : ℕ) (lower : 13≤target) (upper : target+2<46)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (dispatchFetch : FetchesCode program before.pc (solverRuntimeDispatchCode returnPC labels.solveEntry))
    (separatePC : before.pc+14<labels.solveEntry) (returnSeparate : returnPC+20<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (statisticsFetch : FetchesCode program returnPC (rootStatisticsCode target)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38800*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=returnPC+20 ∧ after.register .fresh=.natural (99+2*P.certificate.M) ∧
      after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools) ∧
      after.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length ∧
      HeapList after (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after target
        [.rational (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).observation,
         .rational (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).repairs,
         .rational (P.solveRisk (P.cachedSolveMultiplier P.endpointCache fee penalty))] ∧
      after.output=before.output ∧
      peakCells trace≤workingCells before+65*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state
        (workspace (99+2*P.certificate.M) P.certificate.stages P.tools∪{target,target+1,target+2})) ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 := by
  let base:=99+2*P.certificate.M
  let n:=P.certificate.stages
  let k:=P.tools
  let region:=workspace base n k∪{target,target+1,target+2}
  let record:=P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)
  obtain ⟨solver,computed,sh,sl,sc,st,returned,solverMemory,solverPeak,requests,count,_dense,root⟩:=
    solver_runtime_dense_from_prepared_heap_actual P fee penalty input program labels before returnPC penaltyValue
      prepared stored dispatchFetch separatePC (by omega) stubFetch bodyFetch
  change Return P fee penalty n k base returnPC before computed at returned
  change ∀ state∈solver,RegionMemory before state (workspace base n k) at solverMemory
  change peakCells solver≤workingCells before+62*PDCompute.Solver.entryCount n k at solverPeak
  obtain ⟨pc,fresh,old,address,index,table,output,_frame⟩:=returned
  have computedMemory:=solverMemory computed (List.mem_of_getLast? sl)
  have preparedComputed : HeapList computed 0 (preparedInput P fee) := by
    apply computedMemory.heapList prepared
    intro offset inside member
    change offset<13 at inside
    obtain ⟨position,_bound,equal⟩:=Finset.mem_image.mp member
    change 99+2*P.certificate.M+position=0+offset at equal
    omega
  have fetched : FetchesCode program computed.pc (rootStatisticsCode target) := by rw [pc];exact statisticsFetch
  obtain ⟨statistics,th,tl,tc,tt,statisticsMemory,statisticsPC,statisticsPeak⟩:=
    original_root_statistics_actual P fee penalty program input computed target lower upper preparedComputed address root fetched
  let after:=rootStatisticsResult computed target P.certificate.M record.observation record.repairs record.failure
  change statistics.getLast?=some after at tl
  have tailMemory:=statisticsMemory after (List.mem_of_getLast? tl)
  have finalPC : after.pc=returnPC+20:=by change computed.pc+20=returnPC+20;rw [pc]
  have preparedAfter : HeapList after 0 (preparedInput P fee) := by
    apply tailMemory.heapList preparedComputed
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have tableAfter : HeapList after (resultBase base n k)
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)) := by
    apply tailMemory.heapList table
    intro offset _inside
    have sourceBound:=dense_result_source_bound base n k
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have metadata : HeapList after target
      [.rational record.observation,.rational record.repairs,.rational record.failure] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      change offset<3 at inside
      interval_cases offset <;> simp [after,rootStatisticsResult]
    · intro offset inside
      change offset<3 at inside
      interval_cases offset <;> simp [after,rootStatisticsResult]
  have joined:=joinTrace_spec program input solver statistics before computed after
    (38400*(P.certificate.M+1)*PDCompute.Solver.entryCount n k) 315 sh sl th tl sc tc st tt
  have allMemory : ∀ state∈joinTrace solver statistics,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with solverMember|statisticsMember
    · exact (solverMemory state solverMember).enlarge Finset.subset_union_left
    · exact (computedMemory.enlarge Finset.subset_union_left).trans
        ((statisticsMemory state statisticsMember).enlarge Finset.subset_union_right)
  have positive : 1≤PDCompute.Solver.entryCount n k:=by change 0<(n+1)*(k+1);positivity
  have computedBound:=(workingCells_le_peak_of_member solver computed (List.mem_of_getLast? sl)).trans solverPeak
  have allSpace : ∀ state∈joinTrace solver statistics,
      workingCells state≤workingCells before+65*PDCompute.Solver.entryCount n k := by
    intro state member
    rcases joinTrace_member member with solverMember|statisticsMember
    · have bound:=(workingCells_le_peak_of_member solver state solverMember).trans solverPeak
      omega
    · have bound:=(workingCells_le_peak_of_member statistics state statisticsMember).trans statisticsPeak
      omega
  have noStatistics:=no_solve_entry labels statistics (by
    intro state member
    have bound:=(statisticsPC state member).2
    rw [pc] at bound
    omega)
  have noLast:=no_solve_entry labels [computed] (by
    intro state member
    have same : state=computed:=List.mem_singleton.mp member
    subst state
    rw [pc]
    omega)
  have split:=List.dropLast_append_getLast? computed (by rw [sl];simp)
  have droppedRequests : actualSolveRequests labels solver.dropLast=[penalty] := by
    rw [←split,solveRequests_append,noLast.1,List.append_nil] at requests
    exact requests
  have droppedCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry solver.dropLast=1 := by
    rw [←split,solveEntries_append,noLast.2,Nat.add_zero] at count
    exact count
  refine ⟨joinTrace solver statistics,after,joined.1,joined.2.1,joined.2.2.1,?_,finalPC,rfl,?_,?_,?_,
    tableAfter,preparedAfter,metadata,?_,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    allMemory,?_,?_⟩
  · have product : 0<(P.certificate.M+1)*PDCompute.Solver.entryCount n k:=by positivity
    have budget : 38400*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+315≤
        38800*(P.certificate.M+1)*PDCompute.Solver.entryCount n k := by simp only [Nat.mul_assoc];omega
    exact joined.2.2.2.trans budget
  · change computed.register .old=.natural returnPC
    exact old
  · change computed.register .address=.natural (resultBase base n k)
    exact address
  · change computed.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length
    exact index
  · exact tailMemory.2.2.2.trans output
  · change actualSolveRequests labels (solver.dropLast++statistics)=[penalty]
    rw [solveRequests_append,droppedRequests,noStatistics.1,List.append_nil]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (solver.dropLast++statistics)=1
    rw [solveEntries_append,droppedCount,noStatistics.2,Nat.add_zero]

end RootD27.Core
