module
public import Paid.PDCompute_CoreInitialize_InitialCalls_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section

namespace PDCompute.CoreInitialize
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core RootD27.Bits PDLower.CoreSearch PDLower.CoreRuntimeNumeric

/-- Starting only with the actual prepared input/cache and live Header48,
physically initialization metadata and run both original solves. Neither
metadata, solved tables nor a source search representation is supplied. -/
theorem initialize_search_resources (P : Parameters) (fee : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (initializeSearchCode before.pc labels.solveEntry))
    (belowEntry : before.pc+164<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (limitBits : (Cell.natural ((99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+164)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (zeroRoom : 4194304*solverBitScale P fee 0 P.certificate.stages P.tools≤budget)
    (lambdaRoom : 4194304*solverBitScale P fee P.Lambda P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤85000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+164 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧
      SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 28=.natural (P.bisectionBudget fee) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (initializeSearchRegion P fee)) ∧
      actualSolveRequests labels trace=[0,P.Lambda] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=2 ∧
      (∀ state∈trace,SafeBits state budget) ∧ peakOperandBits trace≤budget ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,ClosedPC labels before.pc (before.pc+164) state) ∧
      (∀ state∈trace.dropLast,ProperPC labels before.pc (before.pc+164) state) ∧
      (∀ state∈trace.dropLast,¬state.pc=before.pc+164) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let region:=initializeSearchRegion P fee
  let initValues:=searchInitializeValues values
  change FetchesCode program before.pc
    (headerCode searchInitializeCommands++initialSolvedCallsCode (before.pc+20) labels.solveEntry) at fetched
  obtain ⟨initialization,initialized,ih,il,ic,it,initHeader,initFresh,initPC,initMemory,initSafe,initScope,initProper⟩:=
    metadata_resources program input before values budget header fresh safe small
      ((natBits_mono (by omega : before.pc+20≤before.pc+164)).trans (by change 1+natBits (before.pc+164)≤budget at endBits;omega))
      fetched.append_left
  have initFinal:=initMemory initialized (List.mem_of_getLast? il)
  have initializedMemory:=scalar_region_memory initFinal
  have preparedInitialized : HeapList initialized 0 (preparedInput P fee) := by
    apply initializedMemory.heapList prepared
    intro offset inside
    change offset<13 at inside
    apply scalarRegion_outside
    exact Or.inl (by omega)
  have cacheInitialized : HeapList initialized 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply initializedMemory.heapList stored
    intro offset _inside
    apply scalarRegion_outside
    exact Or.inr (by omega)
  have lambdaHeap:=PDLower.CalibrationCompute.HeapList.value prepared 11 (by change 11<13;decide)
  have countHeap:=PDLower.CalibrationCompute.HeapList.value prepared 10 (by change 10<13;decide)
  change before.heap 11=.rational P.Lambda at lambdaHeap
  change before.heap 10=.natural (P.bisectionBudget fee) at countHeap
  have lambdaBefore : values 11=.rational P.Lambda:=(header.value 11 (by decide)).symm.trans lambdaHeap
  have countBefore : values 10=.natural (P.bisectionBudget fee):=(header.value 10 (by decide)).symm.trans countHeap
  have tagValue : initValues 13=.natural 1:=by simp [initValues,searchInitializeValues]
  have zeroValue : initValues 14=.rational 0:=by simp [initValues,searchInitializeValues]
  have lambdaValue : initValues 15=.rational P.Lambda:=by simp [initValues,searchInitializeValues,lambdaBefore]
  have countValue : initialized.heap 28=.natural (P.bisectionBudget fee) := by
    simpa [initValues,searchInitializeValues,countBefore] using initHeader.value 28 (by decide)
  have callsFetch : FetchesCode program initialized.pc (initialSolvedCallsCode initialized.pc labels.solveEntry) := by
    have position : initialized.pc=before.pc+20:=initPC
    rw [position]
    simpa only [searchInitialize_length] using fetched.append_right
  obtain ⟨calls,after,ch,cl,cc,ct,afterPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,
    counter,output,callsPeak,callsMemory,requests,count,callsSafe,callsCalls,callsScope,callsProper⟩:=
    initial_solved_resources P fee program labels input initialized initValues initHeader initFresh
      tagValue zeroValue lambdaValue preparedInitialized cacheInitialized callsFetch
      (by change initialized.pc=before.pc+20 at initPC;omega) stubFetch bodyFetch
      budget (initSafe initialized (List.mem_of_getLast? il)) small limitBits
      (by simpa only [initPC,Nat.add_assoc] using endBits) controlRoom zeroRoom lambdaRoom markerLabel
  have joined:=joinTrace_spec program input initialization calls before initialized after 315
    (84000*(P.certificate.M+1)*entries) ih il ch cl ic cc it ct
  have allMemory : ∀ state∈joinTrace initialization calls,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with initialMember|callMember
    · exact (scalar_region_memory (initMemory state initialMember)).enlarge Finset.subset_union_left
    · exact (initializedMemory.enlarge Finset.subset_union_left).trans
        ((callsMemory state callMember).enlarge Finset.subset_union_right)
  have initWorking : workingCells initialized=workingCells before := by
    unfold workingCells
    rw [initFinal.2.2.1,initFinal.2.2.2]
  have allSpace : ∀ state∈joinTrace initialization calls,workingCells state≤workingCells before+156*entries := by
    intro state member
    rcases joinTrace_member member with initialMember|callMember
    · have memory:=initMemory state initialMember
      have same : workingCells state=workingCells before := by
        unfold workingCells
        rw [memory.2.2.1,memory.2.2.2]
      omega
    · have bound:=(workingCells_le_peak_of_member calls state callMember).trans callsPeak
      change workingCells state≤workingCells initialized+156*entries at bound
      omega
  have noInitialize:=no_solve_entry labels initialization.dropLast (by
    intro state member
    have scope:=initScope state (List.mem_of_mem_dropLast member)
    change before.pc≤state.pc ∧ state.pc≤before.pc+20 at scope
    omega)
  have positive : 0<entries:=retained_capacity_positive P.certificate.stages P.tools
  have factor : entries≤(P.certificate.M+1)*entries:=by nlinarith
  have timeBudget : 315+84000*(P.certificate.M+1)*entries≤85000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  have finalPC : after.pc=before.pc+164 := by
    change initialized.pc=before.pc+20 at initPC
    omega
  have initialClosed : ∀ state∈initialization,ClosedPC labels before.pc (before.pc+20) state :=
    fun state member=>Or.inl (initScope state member)
  have callsClosed : ∀ state∈calls,ClosedPC labels (before.pc+20) (before.pc+164) state := by
    simpa only [initPC,Nat.add_assoc] using callsScope
  have callsStrict : ∀ state∈calls.dropLast,ProperPC labels (before.pc+20) (before.pc+164) state := by
    simpa only [initPC,Nat.add_assoc] using callsProper
  have scopes:=join_scope labels initialization calls before.pc (before.pc+20) (before.pc+164)
    (by intro empty;rw [empty] at ch;cases ch) (by omega) (by omega) initialClosed callsClosed callsStrict
  have initialCalls : SolverCallRefinement program labels P fee 40000 initialization :=
    PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee 40000 initialization (by
      intro state member
      have scope:=initScope state member
      omega)
  have joinedCalls:=PDCompute.CoreSearchLoop.refinement_join program labels P fee 40000 initialization calls initialized il ch initialCalls callsCalls
  have joinedSafe:=PDCompute.Pack.joinTrace_invariant initialization calls (fun state=>SafeBits state budget) initSafe callsSafe
  have firstExit : ∀ state∈(joinTrace initialization calls).dropLast,¬state.pc=before.pc+164 := by
    intro state member same
    rcases scopes.2 state member with inline|callee
    · omega
    · exact (by have lower:=callee.1;omega)
  refine ⟨joinTrace initialization calls,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    finalPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,counter.trans countValue,
    output.trans initFinal.2.2.2,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_,joinedSafe,PDCompute.Pack.safeBits_peak _ budget joinedSafe,joinedCalls,scopes.1,scopes.2,firstExit⟩
  · change actualSolveRequests labels (initialization.dropLast++calls)=[0,P.Lambda]
    rw [solveRequests_append,noInitialize.1,requests,List.nil_append]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (initialization.dropLast++calls)=2
    rw [solveEntries_append,noInitialize.2,count,Nat.zero_add]


end PDCompute.CoreInitialize
