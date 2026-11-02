module
public import Common.ROOT_ActualTrace_Resources_003
public import Paid.PDCompute_CorePrelude_Calibration_007
public import Paid.PDCompute_CorePrelude_EntryCount_011
public import Paid.PDCompute_CorePreludePC_Actual_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section
namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.CoreSearchBudget PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDLower.CalibrationCompute (linearExecute)

/-- Same119 actual numeric callee witness, identified with the original
functional entry-count witness before moving entry316=1 into its trace. -/
theorem calibration_counted_resources (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (position : before.pc=302)
    (prepared : HeapList before 0 (preparedInput P fee))
    (cache : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (safe : SafeBits before (endpointBudget P fee))
    (argumentsFetch : FetchesCode program 302 (calibrationHeapArgumentsCode afterCalibration))
    (kernelFetch : FetchesCode program 316 (PDLower.CalibrationCompute.kernel 316).toList) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤30300*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      PDLower.CalibrationCompute.Return P (99+2*P.certificate.M) afterCalibration before after ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      peakCells trace≤workingCells before+8*P.certificate.M+28 ∧
      (∀ state∈trace,SafeBits state (calibrationBudget P fee)) ∧
      (∀ state∈trace,302≤state.pc ∧ state.pc≤afterCalibration) ∧
      (∀ state∈trace.dropLast,state.pc<afterCalibration) ∧
      PaperProofs.Paid.Computation.entryCount 316 trace=1 := by
  let entered:=calibrationHeapArgumentsResult P before afterCalibration
  have positive:=coreOperandBound_positive P fee
  have small : 64≤ inputBudget P fee:=by unfold inputBudget;omega
  have carried:=PDROC.EndpointOperands.carry_le_operandBudget P (inputBudget P fee)
  have returnPCValue : afterCalibration=743:=by
    have start:=initial_body_start_actual
    unfold bodyStart at start
    omega
  have returnBits : (Cell.natural afterCalibration).bits≤endpointBudget P fee:=by
    rw [returnPCValue]
    exact ((by decide : (Cell.natural 743).bits≤64).trans small).trans carried
  have pcBits : natBits (before.pc+14)≤endpointBudget P fee:=by
    rw [position]
    exact ((by decide : natBits (302+14)≤64).trans small).trans carried
  have argsSafe:=calibration_arguments_safe P fee input before afterCalibration (endpointBudget P fee) safe prepared
    ((base_cell_bits P fee).trans carried) returnBits pcBits
  have argsRun:=calibrationHeapArguments_execute P fee input before afterCalibration prepared
  have argsFetch : FetchesCode program before.pc (calibrationHeapArgumentsCode afterCalibration):=by
    rw [position]
    exact argumentsFetch
  obtain ⟨setup,sh,sl,sc,st,setupResources,setupScope,setupProper⟩:=readonly_linear_resources program input
    (calibrationHeapArgumentsCode afterCalibration) before entered (endpointBudget P fee)
    (calibrationHeapArguments_straight _) argsFetch argsRun argsSafe
    (fun count bound state actual=>calibrationHeapArguments_prefix_memory P fee input before state afterCalibration count prepared bound actual)
  have entryPC : entered.pc=PDLower.CalibrationCompute.labelAddress 316 .enter:=by
    rw [PDLower.CalibrationCompute.entry_address]
    change before.pc+14=316
    omega
  obtain ⟨after,body,bh,bl,bc,bt,returned,bodyPeak,_bitPeak,bodySafe⟩:=
    PDLower.CalibrationCompute.callee_resources P 316 (99+2*P.certificate.M) 96 afterCalibration
      (endpointBudget P fee) (ratEncodingBits P.certificate.gamma) input entered
      (calibrationHeapArguments_callArguments P before afterCalibration) (argsSafe.final argsRun) (le_refl _)
      cache (original_endpoint_avoids_calibration P) entryPC
  have originalChain : body.IsChain (fun first later=>
      step (locatedBlock 316 (PDLower.CalibrationCompute.kernel 316).toList.toArray) input first=some later):=by
    simpa only [Array.toArray_toList] using bc
  have embedded:=located_trace_in_program program input 316 (PDLower.CalibrationCompute.kernel 316).toList body kernelFetch originalChain
  have kernelLength : (PDLower.CalibrationCompute.kernel 316).size=427:=by
    simpa only [calibrationEntry,kernel_words_actual] using kernel_length
  have bodyProper : ∀ state∈body.dropLast,316≤state.pc ∧ state.pc<afterCalibration:=by
    intro state member
    have scope:=embedded.2.2 state member
    simp only [Array.length_toList,kernelLength] at scope
    rw [returnPCValue]
    omega
  have afterPC:=returned.1
  have bodyScope : ∀ state∈body,316≤state.pc ∧ state.pc≤afterCalibration:=by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [bl];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have scope:=bodyProper state proper;omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      rw [afterPC,returnPCValue]
      omega
  have endpointAt : PDLower.CalibrationCompute.HeapList entered 96
      (encodeList encodeEndpoint P.endpointCache.toList):=by
    change PDLower.CalibrationCompute.HeapList before 96
      (encodeList encodeEndpoint P.endpointCache.toList)
    simpa only [PDCompute.Solver.HeapList,PDLower.CalibrationCompute.HeapList] using cache
  have callerArguments : PDLower.CalibrationCompute.CallArguments P (99+2*P.certificate.M) 96 743 entered:=by
    have actualArguments : PDLower.CalibrationCompute.CallArguments P (99+2*P.certificate.M) 96 afterCalibration entered:=
      calibrationHeapArguments_callArguments P before afterCalibration
    exact Eq.mp (congrArg (fun returnPC=>
      PDLower.CalibrationCompute.CallArguments P (99+2*P.certificate.M) 96 returnPC entered) returnPCValue) actualArguments
  obtain ⟨functional,functionalAfter,fh,fl,fc,finalPC,_closed,functionalProper,functionalCount⟩:=
    PDCompute.CorePreludePC.calibration_functional_pc P (99+2*P.certificate.M) 96 input entered callerArguments endpointAt
      (original_endpoint_avoids_calibration P) (by simpa only [PDLower.CalibrationCompute.entry_address] using entryPC)
  have identity:=ROOT.ActualTrace.firstExit_unique_of_endpoints
    (fun state=>step (locatedBlock 316 (PDLower.CalibrationCompute.kernel 316)) input state)
    (fun state=>state.pc=743) entered after functionalAfter body functional bh fh bc fc bl fl
    (by simpa only [returnPCValue] using afterPC) finalPC
    (by intro state member;have bound:=(bodyProper state member).2;rw [returnPCValue] at bound;omega)
    (by intro state member;have bound:=(functionalProper state member).2;omega)
  have bodyCount : PaperProofs.Paid.Computation.entryCount 316 body=1:=by
    rw [identity.1]
    exact functionalCount
  have carryToCalibration : endpointBudget P fee≤calibrationBudget P fee:=by
    unfold calibrationBudget PDLower.CalibrationCompute.calleeOperandBudget
    omega
  have firstScope : ∀ state∈setup,302≤state.pc ∧ state.pc≤316:=by
    intro state member
    have scope:=setupScope state member
    rw [position,calibrationHeapArguments_length] at scope
    exact scope
  have joined:=joinTrace_spec program input setup body before entered after 225
    (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15) sh sl bh bl sc embedded.1 st
    (embedded.2.1.trans (Nat.add_le_add_right bt 15))
  change PDLower.CalibrationCompute.Return P (99+2*P.certificate.M) afterCalibration before after at returned
  have frame:=returned.2.2.2.2.2.2.2
  refine ⟨joinTrace setup body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,?_,?_,?_,?_,?_,?_,?_⟩
  · have positiveScale : 0<(P.certificate.Q+1)*(P.certificate.M+1)^2:=by positivity
    have room : 225+(30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15)≤
        30300*(P.certificate.Q+1)*(P.certificate.M+1)^2:=by simp only [Nat.mul_assoc];omega
    exact joined.2.2.2.trans room
  · exact PDLower.CalibrationCompute.HeapList.memoryFrame prepared _ frame
      (fun offset inside=>original_prepared_avoids_calibration P offset inside)
  · exact PDLower.CalibrationCompute.HeapList.memoryFrame cache _ frame (original_endpoint_avoids_calibration P)
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    rcases joinTrace_member member with early|later
    · have memory:=(setupResources state early).1
      simp only [workingCells,memory.2.1,memory.2.2]
      omega
    · have bound:=(workingCells_le_peak_of_member body state later).trans bodyPeak
      rw [PDLower.CalibrationCompute.workspaceSize_linear] at bound
      change workingCells state≤workingCells before+(6*P.certificate.M+25)+(2*P.certificate.M+3) at bound
      omega
  · exact PDCompute.Pack.joinTrace_invariant setup body (fun state=>SafeBits state (calibrationBudget P fee))
      (fun state member=>PDCompute.Pack.safeBits_mono (setupResources state member).2 carryToCalibration) bodySafe
  · intro state member
    rcases joinTrace_member member with early|later
    · have scope:=firstScope state early;rw [returnPCValue];omega
    · have scope:=bodyScope state later;omega
  · apply solverJoinTrace_proper setup body entered (fun state=>state.pc<afterCalibration) sl bh
    · intro state member;have scope:=firstScope state member;rw [returnPCValue];omega
    · intro state member;exact (bodyProper state member).2

  · have noSetup : PaperProofs.Paid.Computation.entryCount 316 setup.dropLast=0:=
      (no_solve_entry ⟨316,0,0,0⟩ setup.dropLast (by
        intro state member
        have bound:=setupProper state member
        rw [calibrationHeapArguments_length,position] at bound
        change state.pc≠316
        omega)).2
    change PaperProofs.Paid.Computation.entryCount 316 (setup.dropLast++body)=1
    rw [solveEntries_append ⟨316,0,0,0⟩,noSetup,bodyCount,Nat.zero_add]

end PDCompute.CorePrelude
