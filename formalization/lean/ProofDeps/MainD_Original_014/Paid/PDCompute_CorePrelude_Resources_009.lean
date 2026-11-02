module
public import Paid.PDCompute_CorePrelude_Header_008
public import Paid.PDCompute_CoreSearchLoop_CallWindows_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits

/-- Original prepared13 input and actual initial state, through physical
loading, endpoint computation/output, one calibration computation/output
and Header48 establishment. Every resource concerns this ONE actual
trace at the original global B. The two routine-entry counts are proved
by the later scoped refinement, not supplied as assumptions here. -/
theorem actual_prefix_resources (suffix : Program) (P : Parameters) (fee : ℚ)
    (pcUpper solveEntry solveReturn : ℕ) (solverOutside : bodyStart<solveEntry) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (program suffix) (preparedInput P fee) first=some later) ∧
      time (program suffix) trace≤8800*(P.certificate.M+1)+
        30300*(P.certificate.Q+1)*(P.certificate.M+1)^2+2535 ∧
      after.pc=bodyStart ∧ PDCompute.CoreSearchLoop.Ready P fee after ∧
      HeapList after (PDLower.CalibrationCompute.resultBase (99+2*P.certificate.M) P.certificate.M)
        (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) ∧
      after.output=encodeList encodeEndpoint P.endpointCache.toList++
        encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      peakCells trace≤150*(P.certificate.M+1) ∧
      (∀ state∈trace,SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) ∧
      (∀ state∈trace,state.pc≤bodyStart) ∧ (∀ state∈trace.dropLast,state.pc<bodyStart) ∧
      actualSolveRequests (routineLabels solveEntry solveReturn) trace=[] ∧
      PaperProofs.Paid.Computation.entryCount solveEntry trace=0 ∧
      SolverCallRefinement (program suffix) (routineLabels solveEntry solveReturn) P fee 40000 trace := by
  let actualProgram:=program suffix
  have literal : FetchesCode actualProgram 0 (actualProgram.toList):=by
    intro offset inside
    simp only [Nat.zero_add,Array.getElem?_toList]
  change FetchesCode (program suffix) 0 ((program suffix).toList) at literal
  rw [program_toList] at literal
  have copyFetch : FetchesCode actualProgram 0 (inputCopyCode 13):=literal.append_left
  obtain ⟨loading,lh,ll,lc,lt,loadResources,loadScope,loadProper,prepared⟩:=prepared_loader_resources P fee actualProgram copyFetch
  let loaded:=inputCopyResult (preparedInput P fee) initial 13
  have loadedPC : loaded.pc=39:=by rw [inputCopy_pc];rfl
  have endpointFetch : FetchesCode actualProgram 39 (endpointHeapOutputCode 39 48 96 302):=by
    simpa only [inputCopy_length,Nat.zero_add] using literal.append_right.append_left
  obtain ⟨endpoint,computed,eh,el,ec,et,computedPC,preparedComputed,cacheComputed,computedOutput,
    endpointPeak,endpointSafe,endpointScope,_endpointProper⟩:=endpoint_output_resources P fee actualProgram (preparedInput P fee)
      loaded loadedPC prepared (loadResources loaded (List.mem_of_getLast? ll)).2 endpointFetch
  have argumentsFetch : FetchesCode actualProgram 302 (calibrationHeapArgumentsCode afterCalibration):=by
    simpa only [inputCopy_length,endpointHeapOutput_length,Nat.zero_add] using literal.append_right.append_right.append_left
  have kernelFetch : FetchesCode actualProgram 316 (PDLower.CalibrationCompute.kernel 316).toList:=by
    simpa only [inputCopy_length,endpointHeapOutput_length,calibrationHeapArguments_length,Nat.zero_add] using
      literal.append_right.append_right.append_right.append_left
  obtain ⟨calibration,calibrated,ch,cl,cc,ct,returned,preparedCalibrated,cacheCalibrated,
    calibrationPeak,calibrationSafe,calibrationScope,_calibrationProper⟩:=calibration_resources P fee actualProgram (preparedInput P fee)
      computed computedPC preparedComputed cacheComputed (endpointSafe computed (List.mem_of_getLast? el)) argumentsFetch kernelFetch
  have kernelLength : (PDLower.CalibrationCompute.kernel 316).size=427:=by
    simpa only [calibrationEntry,kernel_words_actual] using kernel_length
  have returnPCValue : afterCalibration=743:=by
    have start:=initial_body_start_actual
    unfold bodyStart at start
    omega
  have headerFetch : FetchesCode actualProgram afterCalibration (PDCompute.CorePrelude.headerCode afterCalibration):=by
    simpa only [inputCopy_length,endpointHeapOutput_length,calibrationHeapArguments_length,
      Array.length_toList,kernelLength,returnPCValue,Nat.zero_add] using literal.append_right.append_right.append_right.append_right.append_left
  obtain ⟨header,after,hh,hl,hc,ht,afterPC,ready,afterOutput,headerPeak,headerMemory,headerSafe,headerScope,headerProper⟩:=
    header_resources P fee actualProgram (preparedInput P fee) calibrated returned.1 preparedCalibrated cacheCalibrated
      (calibrationSafe calibrated (List.mem_of_getLast? cl)) headerFetch
  have joined1:=joinTrace_spec actualProgram (preparedInput P fee) loading endpoint initial loaded computed
    795 (8000*(P.certificate.M+1)) lh ll eh el lc ec lt et
  have joined2:=joinTrace_spec actualProgram (preparedInput P fee) (joinTrace loading endpoint) calibration initial computed calibrated
    (795+8000*(P.certificate.M+1)) (30300*(P.certificate.Q+1)*(P.certificate.M+1)^2)
    joined1.1 joined1.2.1 ch cl joined1.2.2.1 cc joined1.2.2.2 ct
  have joined:=joinTrace_spec actualProgram (preparedInput P fee) (joinTrace (joinTrace loading endpoint) calibration) header
    initial calibrated after
    (795+8000*(P.certificate.M+1)+30300*(P.certificate.Q+1)*(P.certificate.M+1)^2) 2535
    joined2.1 joined2.2.1 hh hl joined2.2.2.1 hc joined2.2.2.2 ht
  let trace:=joinTrace (joinTrace (joinTrace loading endpoint) calibration) header
  have copyBound (state : State) (member : state∈loading) : workingCells state≤20:=
    inputCopy_workingCells initial state 13 (loadResources state member).1
  have loadedBound:=copyBound loaded (List.mem_of_getLast? ll)
  have computedBound:=(workingCells_le_peak_of_member endpoint computed (List.mem_of_getLast? el)).trans endpointPeak
  have calibratedBound:=(workingCells_le_peak_of_member calibration calibrated (List.mem_of_getLast? cl)).trans calibrationPeak
  have allSpace : ∀ state∈trace,workingCells state≤150*(P.certificate.M+1):=by
    intro state member
    rcases joinTrace_member member with earlier|last
    · rcases joinTrace_member earlier with first|middle
      · rcases joinTrace_member first with copying|endpoints
        · have bound:=copyBound state copying;omega
        · have bound:=(workingCells_le_peak_of_member endpoint state endpoints).trans endpointPeak;omega
      · have bound:=(workingCells_le_peak_of_member calibration state middle).trans calibrationPeak;omega
    · have bound:=(workingCells_le_peak_of_member header state last).trans headerPeak;omega
  have carry1:=PDROC.EndpointOperands.carry_le_operandBudget P (inputBudget P fee)
  have carry2 : endpointBudget P fee≤calibrationBudget P fee:=by
    unfold calibrationBudget PDLower.CalibrationCompute.calleeOperandBudget;omega
  have carry3 : calibrationBudget P fee≤prefixBudget P fee:=by
    have room:=(prefix_certificate_bounds P fee).2.2;omega
  have globalRoom:=existing_global_budget_suffices P fee pcUpper
  have allSafe : ∀ state∈trace,SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper):=by
    intro state member
    rcases joinTrace_member member with earlier|last
    · rcases joinTrace_member earlier with first|middle
      · rcases joinTrace_member first with copying|endpoints
        · exact PDCompute.Pack.safeBits_mono (loadResources state copying).2 (carry1.trans (carry2.trans (carry3.trans globalRoom)))
        · exact PDCompute.Pack.safeBits_mono (endpointSafe state endpoints) (carry2.trans (carry3.trans globalRoom))
      · exact PDCompute.Pack.safeBits_mono (calibrationSafe state middle) (carry3.trans globalRoom)
    · exact PDCompute.Pack.safeBits_mono (headerSafe state last) globalRoom
  have earlyScope : ∀ state∈joinTrace (joinTrace loading endpoint) calibration,state.pc≤afterCalibration:=by
    intro state member
    rcases joinTrace_member member with first|last
    · rcases joinTrace_member first with copying|endpoints
      · have bound:=loadScope state copying;rw [returnPCValue];omega
      · have bound:=(endpointScope state endpoints).2;rw [returnPCValue];omega
    · exact (calibrationScope state last).2
  have allScope : ∀ state∈trace,state.pc≤bodyStart:=by
    intro state member
    rcases joinTrace_member member with earlier|last
    · have bound:=earlyScope state earlier;unfold bodyStart;omega
    · exact (headerScope state last).2
  have proper : ∀ state∈trace.dropLast,state.pc<bodyStart:=by
    apply solverJoinTrace_proper _ header calibrated (fun state=>state.pc<bodyStart) joined2.2.1 hh
    · intro state member;have bound:=earlyScope state member;unfold bodyStart;omega
    · exact headerProper
  have noEntry : ∀ state∈trace,state.pc≠solveEntry:=by
    intro state member;have bound:=allScope state member;omega
  have noSolve:=no_solve_entry (routineLabels solveEntry solveReturn) trace (by
    intro state member;exact noEntry state member)
  have calls:=PDCompute.CoreSearchLoop.refinement_of_no_entry actualProgram (routineLabels solveEntry solveReturn)
    P fee 40000 trace noEntry
  have calibrationStored:=returned.2.2.2.2.2.1
  have retainedCalibration : HeapList after (PDLower.CalibrationCompute.resultBase (99+2*P.certificate.M) P.certificate.M)
      (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList):=by
    apply (headerMemory after (List.mem_of_getLast? hl)).heapList calibrationStored
    intro offset inside
    rw [mem_cellRegion_iff]
    unfold PDLower.CalibrationCompute.resultBase
    omega
  have stream:=returned.2.2.2.2.2.2.1
  have loadedOutput : loaded.output=[]:=inputCopy_output (preparedInput P fee) initial 13
  refine ⟨trace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans (by omega),afterPC,ready,
    retainedCalibration,?_,PDLower.CalibrationCompute.peakCells_le_of_forall trace _ allSpace,allSafe,allScope,proper,
    noSolve.1,noSolve.2,calls⟩
  rw [afterOutput,stream,computedOutput,loadedOutput,List.nil_append]

end PDCompute.CorePrelude
