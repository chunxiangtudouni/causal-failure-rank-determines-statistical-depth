module

public import Paid.PDLower_CoreRuntimeNumeric_RootStatistics_004
public import Paid.PDLower_CoreRuntimeNumeric_Complete_012
public import Paid.RootD27Core_CacheLayout_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDLower.CoreRuntimeNumeric

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver PDCompute.NatControl RootD27.Core RootD27.Bits PDCompute.CoreSearchLoop

/-- Real runtime-penalty argument reads, actual dispatch jump, actual common
entry and complete solver with true indirect return. The shared arrival
is removed exactly once. All resource/log conclusions use ONE trace. -/
theorem runtime_solver_marked_resources (P : Parameters) (fee penalty : ℚ) (input : List Cell)
    (program : Program) (labels : RoutineLabels) (before : State) (returnPC : ℕ)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (dispatchFetch : FetchesCode program before.pc (solverRuntimeDispatchCode returnPC labels.solveEntry))
    (separatePC : before.pc+(solverRuntimeArgumentsCode returnPC).length<labels.solveEntry)
    (returnSeparate : returnPC<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+14)≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels)
    :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38400*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      Return P fee penalty P.certificate.stages P.tools
        (99+2*P.certificate.M) returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace (99+2*P.certificate.M) P.certificate.stages P.tools)) ∧
      peakCells trace≤workingCells before+62*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      DenseOriginalTable after P fee penalty (99+2*P.certificate.M) P.certificate.stages P.tools ∧
      PDLower.CalibrationCompute.HeapList after (cellBase (99+2*P.certificate.M) P.tools P.certificate.stages P.tools)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) P.certificate.stages P.tools)) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace.dropLast,(before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
        (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length)) ∧
      SolverCallRefinement program labels P fee 40000 trace := by
  let middle:=solverRuntimeArgumentsResult P fee before returnPC
  let entered : State:={middle with pc:=labels.solveEntry}
  change FetchesCode program before.pc (solverRuntimeArgumentsCode returnPC++[.jump labels.solveEntry]) at dispatchFetch
  have context := runtime_control_context P (labels.solveEntry+1) budget controlRoom
  obtain ⟨setup,sh,sl,sc,st,setupProperties,pcs,_setupProper,_setupPeak⟩ :=
    arguments_resources P fee program input before returnPC budget safe prepared (by omega) baseBits returnBits pcBits dispatchFetch.append_left
  have memory : ∀ state∈setup,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output :=
    fun state member => (setupProperties state member).1
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
  have argumentLength := solverRuntimeArguments_length returnPC
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
  have enteredSafe : SafeBits entered budget :=
    ((setupProperties middle (List.mem_of_getLast? sl)).2).withPC labels.solveEntry (context.pc _ (by omega))
  have indexBits : 1+natBits (P.certificate.M+1)≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : P.certificate.M+1≤99+2*P.certificate.M)) 1).trans baseBits
  have sourceBits : 1+natBits (96+(1+2*(P.certificate.M+1)))≤budget := by
    have same : 96+(1+2*(P.certificate.M+1))=99+2*P.certificate.M := by omega
    rw [same]
    exact baseBits
  obtain ⟨body,after,bh,bl,bc,bt,returned,bodyMemory,bodyPeak,bodyRequests,bodyCount,dense,root,bodySafe,bodyScope⟩:=
    stub_resources .liveHeap program input labels P fee penalty entered
      (99+2*P.certificate.M) P.certificate.stages P.tools 96 returnPC rfl (by omega)
      stubFetch bodyFetch rfl rfl rfl penaltyValue rfl rfl rfl endpoint
      (original_endpoint_avoids_solver P P.certificate.stages P.tools)
      _ _ budget context enteredSafe scalarRoom indexBits sourceBits
  have bodyCalls := (stub_trace_calls P fee penalty program input labels entered after body returnPC budget rfl returnSeparate
    stubFetch bodyFetch rfl rfl rfl penaltyValue rfl rfl rfl endpoint enteredSafe baseBits controlRoom scalarRoom markerLabel
    bh bl bc bt returned bodyCount (fun state member => (bodyScope state member).1)).2
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
  have dispatchSafe : ∀ state∈setup++[entered],SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|arrivalMember
    · exact (setupProperties state earlier).2
    · have same := List.mem_singleton.mp arrivalMember
      subst state
      exact enteredSafe
  have allSafe := PDCompute.Pack.joinTrace_invariant (setup++[entered]) body
    (fun state => SafeBits state budget) dispatchSafe bodySafe
  have bodyNonempty : body≠[] := by intro empty;simp [empty] at bh
  have proper : ∀ state∈(joinTrace (setup++[entered]) body).dropLast,
      (before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
      (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) := by
    intro state member
    change state∈((setup++[entered]).dropLast++body).dropLast at member
    rw [List.dropLast_append_of_ne_nil bodyNonempty] at member
    rcases List.mem_append.mp member with dispatchMember|bodyMember
    · have original : state∈setup := by simpa using dispatchMember
      exact Or.inl (pcs state original)
    · exact Or.inr (bodyScope state bodyMember)
  have setupCalls : SolverCallRefinement program labels P fee 40000 setup :=
    refinement_of_no_entry program labels P fee 40000 setup (by
      intro state member same
      have high := (pcs state member).2
      omega)
  have calls : SolverCallRefinement program labels P fee 40000 (joinTrace (setup++[entered]) body) := by
    simpa only [joinTrace,List.dropLast_concat] using
      (refinement_append program labels P fee 40000 setup body setupCalls bodyCalls)
  refine ⟨joinTrace (setup++[entered]) body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,
    allMemory,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,?_,?_,dense,root,allSafe,proper,calls⟩
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

/-- A real arbitrary runtime penalty request, complete original solver,
true indirect return, and physical root-statistics reads in ONE trace.
Neither the table nor its risk/cost record is supplied as input. -/
theorem runtime_statistics_marked_resources (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (target returnPC : ℕ) (lower : 13≤target) (upper : target+2<46)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (dispatchFetch : FetchesCode program before.pc (solverRuntimeDispatchCode returnPC labels.solveEntry))
    (separatePC : before.pc+14<labels.solveEntry) (returnSeparate : returnPC+20<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (statisticsFetch : FetchesCode program returnPC (rootStatisticsCode target))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+14)≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels)
    (statisticsPCBits : natBits (returnPC+20)≤budget) :
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
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
        (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) ∨
        (returnPC≤state.pc ∧ state.pc≤returnPC+20)) ∧
      (∀ state∈trace.dropLast,(before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
        (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) ∨
        (returnPC≤state.pc ∧ state.pc<returnPC+20)) ∧
      (∃ computed∈trace,Return P fee penalty P.certificate.stages P.tools (99+2*P.certificate.M) returnPC before computed) ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList)) ∧
      (24∉({target,target+1,target+2}:Finset ℕ) → after.heap 24=before.heap 24) ∧
      peakOperandBits trace≤budget := by
  let base:=99+2*P.certificate.M
  let n:=P.certificate.stages
  let k:=P.tools
  let region:=workspace base n k∪{target,target+1,target+2}
  let record:=P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)
  obtain ⟨solver,computed,sh,sl,sc,st,returned,solverMemory,solverPeak,requests,count,_dense,root,solverSafe,solverScope,solverCalls⟩:=
    runtime_solver_marked_resources P fee penalty input program labels before returnPC penaltyValue
      prepared stored dispatchFetch separatePC (by omega) stubFetch bodyFetch
      budget safe small baseBits returnBits pcBits controlRoom scalarRoom markerLabel
  have actualReturn := returned
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
  have menuLive : 7∈computed.live := preparedComputed.1 7 (by change 7<13;decide)
  have menuValue := PDLower.CalibrationCompute.HeapList.value preparedComputed 7 (by change 7<13;decide)
  change computed.heap 7=.natural P.certificate.M at menuValue
  obtain ⟨statistics,th,tl,tc,tt,statisticsProperties,statisticsPC,statisticsProper,statisticsPeak⟩:=
    statistics_resources program input computed target (resultBase base n k) P.certificate.M budget
      record.observation record.repairs record.failure lower upper (dense_result_source_bound _ _ _) address
      (dense_root_statistics_heap computed _ _ _ _ root) menuLive menuValue
      (solverSafe computed (List.mem_of_getLast? sl)) small baseBits
      (by simpa only [pc] using statisticsPCBits) fetched
  have statisticsMemory : ∀ state∈statistics,RegionMemory computed state {target,target+1,target+2} :=
    fun state member => (statisticsProperties state member).1
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
  have allSafe := PDCompute.Pack.joinTrace_invariant solver statistics (fun state => SafeBits state budget)
    solverSafe (fun state member => (statisticsProperties state member).2)
  have statisticsNonempty : statistics≠[] := by intro empty;simp [empty] at th
  have proper : ∀ state∈(joinTrace solver statistics).dropLast,
      (before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
      (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) ∨
      (returnPC≤state.pc ∧ state.pc<returnPC+20) := by
    intro state member
    change state∈(solver.dropLast++statistics).dropLast at member
    rw [List.dropLast_append_of_ne_nil statisticsNonempty] at member
    rcases List.mem_append.mp member with solverMember|statisticsMember
    · rcases solverScope state solverMember with inline|body
      · exact Or.inl inline
      · exact Or.inr (Or.inl body)
    · have low := (statisticsPC state (List.mem_of_mem_dropLast statisticsMember)).1
      have high := statisticsProper state statisticsMember
      rw [pc] at low high
      exact Or.inr (Or.inr ⟨low,high⟩)
  have closed : ∀ state∈joinTrace solver statistics,
      (before.pc≤state.pc ∧ state.pc≤before.pc+14) ∨
      (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) ∨
      (returnPC≤state.pc ∧ state.pc≤returnPC+20) := by
    intro state member
    have split := List.dropLast_append_getLast? after (by rw [joined.2.1];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with earlier|terminal
    · rcases proper state earlier with inline|body|tail
      · exact Or.inl inline
      · exact Or.inr (Or.inl body)
      · exact Or.inr (Or.inr ⟨tail.1,tail.2.le⟩)
    · have same := List.mem_singleton.mp terminal
      subst state
      exact Or.inr (Or.inr (by rw [finalPC];omega))
  have computedIn : computed∈joinTrace solver statistics := by
    apply List.mem_append.mpr
    exact Or.inr (List.mem_of_head? th)
  have statisticsCalls : SolverCallRefinement program labels P fee 40000 statistics :=
    refinement_of_no_entry program labels P fee 40000 statistics (by
      intro state member same
      have high := (statisticsPC state member).2
      rw [pc] at high
      omega)
  have calls := refinement_join program labels P fee 40000 solver statistics computed sl th solverCalls statisticsCalls
  have cache : ∀ state∈joinTrace solver statistics,HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList) :=
    fun state member => original_cache_of_runtime_region P before state target upper stored (allMemory state member)
  have lambdaFrame : 24∉({target,target+1,target+2}:Finset ℕ) → after.heap 24=before.heap 24 := by
    intro outside
    apply (RegionMemory.trace_last allMemory joined.2.1).1
    intro member
    rcases Finset.mem_union.mp member with work|statsMember
    · obtain ⟨offset,_inside,equal⟩ := Finset.mem_image.mp work
      change 99+2*P.certificate.M+offset=24 at equal
      omega
    · exact outside statsMember
  refine ⟨joinTrace solver statistics,after,joined.1,joined.2.1,joined.2.2.1,?_,finalPC,rfl,?_,?_,?_,
    tableAfter,preparedAfter,metadata,?_,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    allMemory,?_,?_,allSafe,closed,proper,⟨computed,computedIn,actualReturn⟩,calls,cache,lambdaFrame,safe_trace_peak _ budget allSafe⟩
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


end PDLower.CoreRuntimeNumeric
